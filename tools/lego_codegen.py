#!/usr/bin/env python3
"""
lego_codegen.py — Generate Lean 4 source from JSON layout specifications.

Reads a JSON layout spec (conforming to lego_schema.json) and emits:
  1. A Lean 4 file with the layout definition + bijectivity proof (via DSL macro)
  2. Oracle registration for `lake exe oracle` verification
  3. Optional #guard inline assertions (checked at `lake build` time)

Usage:
    python tools/lego_codegen.py spec.json
    python tools/lego_codegen.py spec.json --output-dir LegoLean/Generated
    python tools/lego_codegen.py spec.json --no-oracle
    python tools/lego_codegen.py spec.json --dry-run

The generated file is placed in LegoLean/Generated/<ModuleName>.lean and
LegoLean/Generated.lean is updated with the new import.
"""

import json
import sys
import os
import argparse
import math
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Validation
# ---------------------------------------------------------------------------

def validate_spec(spec: Dict[str, Any]) -> None:
    """Validate a JSON layout spec. Raises ValueError on problems."""
    required = ["name", "kind", "shape", "tiles"]
    for field in required:
        if field not in spec:
            raise ValueError(f"Missing required field: '{field}'")

    name = spec["name"]
    if not re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*$', name):
        raise ValueError(f"Invalid name: '{name}' (must be a valid Lean identifier)")

    kind = spec["kind"]
    if kind not in ("full_layout", "expand_layout"):
        raise ValueError(f"Invalid kind: '{kind}'")

    shape = spec["shape"]
    d = len(shape)
    if d < 1 or d > 6:
        raise ValueError(f"Shape dimension {d} out of range [1, 6]")
    if any(s < 1 for s in shape):
        raise ValueError(f"Shape entries must be >= 1, got {shape}")

    if kind == "expand_layout":
        if "orig_shape" not in spec:
            raise ValueError("expand_layout requires 'orig_shape'")
        orig = spec["orig_shape"]
        if len(orig) != d:
            raise ValueError(
                f"orig_shape dimension {len(orig)} != shape dimension {d}")
        for i in range(d):
            if orig[i] > shape[i]:
                raise ValueError(
                    f"orig_shape[{i}]={orig[i]} > shape[{i}]={shape[i]}")
            if orig[i] < 1:
                raise ValueError(f"orig_shape entries must be >= 1")

    tiling_mode = spec.get("tiling_mode", "tileby")
    if tiling_mode not in ("tileby", "groupby"):
        raise ValueError(f"Invalid tiling_mode: '{tiling_mode}'")

    tiles = spec["tiles"]
    if len(tiles) < 1 or len(tiles) > 5:
        raise ValueError(f"Number of tiles {len(tiles)} out of range [1, 5]")

    for i, tile in enumerate(tiles):
        if "dims" not in tile:
            raise ValueError(f"Tile {i} missing 'dims'")
        if len(tile["dims"]) != d:
            raise ValueError(
                f"Tile {i} dims length {len(tile['dims'])} != shape dims {d}")
        if any(x < 1 for x in tile["dims"]):
            raise ValueError(f"Tile {i} dims must be >= 1")

        perm = tile.get("perm", {"type": "row"})
        validate_perm(perm, d, tile["dims"], i)

    # Check tiling product = shape along each dimension
    for dim_idx in range(d):
        product = 1
        for tile in tiles:
            product *= tile["dims"][dim_idx]
        if product != shape[dim_idx]:
            raise ValueError(
                f"Tiling product mismatch on dim {dim_idx}: "
                f"{product} != {shape[dim_idx]}")


def validate_perm(perm: Dict[str, Any], d: int, tile_dims: List[int],
                  tile_idx: int) -> None:
    """Validate a permutation specification."""
    ptype = perm.get("type", "row")

    if ptype == "row":
        return
    if ptype == "col":
        if d < 2:
            raise ValueError(f"Tile {tile_idx}: 'col' requires d >= 2")
        return
    if ptype == "regP":
        sigma = perm.get("sigma")
        if sigma is None:
            raise ValueError(f"Tile {tile_idx}: regP requires 'sigma'")
        if len(sigma) != d:
            raise ValueError(
                f"Tile {tile_idx}: sigma length {len(sigma)} != d={d}")
        if sorted(sigma) != list(range(d)):
            raise ValueError(
                f"Tile {tile_idx}: sigma {sigma} is not a permutation of "
                f"[0..{d-1}]")
        return
    if ptype == "genP":
        N = math.prod(tile_dims)
        table = perm.get("table")
        inv_table = perm.get("inv_table")
        if table is None or inv_table is None:
            raise ValueError(
                f"Tile {tile_idx}: genP requires 'table' and 'inv_table'")
        if len(table) != N:
            raise ValueError(
                f"Tile {tile_idx}: table length {len(table)} != tile product {N}")
        if len(inv_table) != N:
            raise ValueError(
                f"Tile {tile_idx}: inv_table length {len(inv_table)} != "
                f"tile product {N}")
        if sorted(table) != list(range(N)):
            raise ValueError(
                f"Tile {tile_idx}: table is not a permutation of [0..{N-1}]")
        if sorted(inv_table) != list(range(N)):
            raise ValueError(
                f"Tile {tile_idx}: inv_table is not a permutation of "
                f"[0..{N-1}]")
        # Verify they are actually inverses
        for i in range(N):
            if inv_table[table[i]] != i:
                raise ValueError(
                    f"Tile {tile_idx}: inv_table[table[{i}]] = "
                    f"{inv_table[table[i]]} != {i}")
            if table[inv_table[i]] != i:
                raise ValueError(
                    f"Tile {tile_idx}: table[inv_table[{i}]] = "
                    f"{table[inv_table[i]]} != {i}")
        if N > 5000:
            print(f"WARNING: Tile {tile_idx} genP table has {N} entries. "
                  f"native_decide may be slow.", file=sys.stderr)
        return

    raise ValueError(f"Tile {tile_idx}: unknown perm type '{ptype}'")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def name_to_module(name: str) -> str:
    """Convert snake_case layout name to CamelCase module name."""
    return "".join(word.capitalize() for word in name.split("_"))


def compute_inverse_sigma(sigma: List[int]) -> List[int]:
    """Compute the inverse of a permutation list."""
    inv = [0] * len(sigma)
    for i, s in enumerate(sigma):
        inv[s] = i
    return inv


# ---------------------------------------------------------------------------
# Lean code generation for permutations
# ---------------------------------------------------------------------------

def gen_perm_lean(name: str, perm: Optional[Dict[str, Any]], d: int,
                  tile_dims: List[int], tile_idx: int
                  ) -> Tuple[str, str]:
    """
    Generate Lean code for a permutation at one tiling level.

    Returns (auxiliary_defs, dsl_suffix).
    - auxiliary_defs: Lean definitions to prepend (empty for simple cases)
    - dsl_suffix: what follows the tile dims in the DSL (e.g., " with col")
    """
    if perm is None:
        perm = {"type": "row"}

    ptype = perm.get("type", "row")

    # ---- row (identity) ----
    if ptype == "row":
        return ("", "")

    # ---- col (dimension reversal) ----
    if ptype == "col":
        return ("", " with col")

    # ---- regP (dimension permutation) ----
    if ptype == "regP":
        sigma = perm["sigma"]

        # Identity shortcut
        if sigma == list(range(d)):
            return ("", "")

        # 2D swap shortcut
        if d == 2 and sigma == [1, 0]:
            return ("", " with regP (Equiv.swap (0 : Fin 2) (1 : Fin 2))")

        # General case: build Equiv.Perm via forward/inverse tables
        inv_sigma = compute_inverse_sigma(sigma)
        prefix = f"{name}_regp{tile_idx}"
        fwd_entries = ", ".join(str(s) for s in sigma)
        inv_entries = ", ".join(str(s) for s in inv_sigma)

        aux = (
            f"private def {prefix}_fwd : Fin {d} → Fin {d} := "
            f"![{fwd_entries}]\n"
            f"private def {prefix}_inv : Fin {d} → Fin {d} := "
            f"![{inv_entries}]\n"
            f"private def {prefix} : Equiv.Perm (Fin {d}) where\n"
            f"  toFun := {prefix}_fwd\n"
            f"  invFun := {prefix}_inv\n"
            f"  left_inv := by native_decide\n"
            f"  right_inv := by native_decide\n"
        )
        return (aux, f" with regP {prefix}")

    # ---- genP (general bijection via tables) ----
    if ptype == "genP":
        table = perm["table"]
        inv_table = perm["inv_table"]
        N = math.prod(tile_dims)
        prefix = f"{name}_genp{tile_idx}"
        shape_vec = ", ".join(str(x) for x in tile_dims)

        fwd_entries = ", ".join(str(x) for x in table)
        inv_entries = ", ".join(str(x) for x in inv_table)

        aux = (
            f"private def {prefix}_fwd : Fin {N} → Fin {N} := "
            f"![{fwd_entries}]\n"
            f"private def {prefix}_inv : Fin {N} → Fin {N} := "
            f"![{inv_entries}]\n"
            f"private def {prefix}_flat : Fin {N} ≃ Fin {N} where\n"
            f"  toFun := {prefix}_fwd\n"
            f"  invFun := {prefix}_inv\n"
            f"  left_inv := by native_decide\n"
            f"  right_inv := by native_decide\n"
            f"\n"
            f"private def {prefix} : "
            f"MultiIndex (![{shape_vec}] : Shape {d}) ≃ "
            f"FlatIndex (![{shape_vec}] : Shape {d}) :=\n"
            f"  let h : Shape.prod (![{shape_vec}] : Shape {d}) = {N} := "
            f"by native_decide\n"
            f"  (B ![{shape_vec}]).trans "
            f"(((finCongr h).trans {prefix}_flat).trans (finCongr h).symm)\n"
        )
        return (aux, f" with genP {prefix}")

    raise ValueError(f"Unknown perm type: '{ptype}'")


# ---------------------------------------------------------------------------
# Main Lean file generation
# ---------------------------------------------------------------------------

def generate_lean(spec: Dict[str, Any], *, include_oracle: bool = True
                  ) -> str:
    """Generate the full Lean 4 source file from a validated spec."""
    name = spec["name"]
    kind = spec["kind"]
    shape = spec["shape"]
    d = len(shape)
    tiling_mode = spec.get("tiling_mode", "tileby")
    tiles = spec["tiles"]
    checks = spec.get("checks", [])

    lines: List[str] = []

    # ---- Header ----
    lines.append("/-")
    lines.append(f"  Auto-generated by tools/lego_codegen.py")
    lines.append(f"  Layout: {name}")
    lines.append(f"  Kind: {kind}, Tiling: {tiling_mode}")
    lines.append(f"  Shape: {shape}")
    if kind == "expand_layout":
        lines.append(f"  Original shape: {spec['orig_shape']}")
    lines.append("-/")
    lines.append("")
    lines.append("import LegoLean.Adapter.OracleLib")
    lines.append("")
    lines.append("namespace LegoLean.Adapter.Generated")
    lines.append("")

    # ---- Auxiliary permutation definitions ----
    aux_blocks: List[str] = []
    perm_suffixes: List[str] = []

    for i, tile in enumerate(tiles):
        perm = tile.get("perm")
        aux, suffix = gen_perm_lean(name, perm, d, tile["dims"], i)
        aux_blocks.append(aux)
        perm_suffixes.append(suffix)

    for aux in aux_blocks:
        if aux.strip():
            lines.append(aux)

    # ---- DSL macro invocation ----
    shape_str = ", ".join(str(x) for x in shape)

    tile_lines: List[str] = []
    for i, tile in enumerate(tiles):
        dims_str = ", ".join(str(x) for x in tile["dims"])
        tile_lines.append(f"  [{dims_str}]{perm_suffixes[i]}")
    tiles_block = ",\n".join(tile_lines)

    if kind == "full_layout":
        lines.append(
            f"lego_full_layout {name} : [{shape_str}] {tiling_mode} [")
        lines.append(tiles_block)
        lines.append("]")
    elif kind == "expand_layout":
        orig_str = ", ".join(str(x) for x in spec["orig_shape"])
        lines.append(
            f"lego_expand_layout {name} : [{orig_str}] \u2192 "
            f"[{shape_str}] {tiling_mode} [")
        lines.append(tiles_block)
        lines.append("]")

    lines.append("")

    # ---- #guard assertions ----
    if checks:
        for check in checks:
            coords = check["coords"]
            expected = check["expected"]
            coords_str = ", ".join(str(x) for x in coords)
            if expected is None:
                lines.append(
                    f"#guard evalLayout {name} [{coords_str}] == none")
            else:
                lines.append(
                    f"#guard evalLayout {name} [{coords_str}] == some "
                    f"{expected}")
        lines.append("")

    # ---- Oracle registration ----
    if include_oracle:
        shape_list = ", ".join(str(x) for x in shape)
        lines.append(f"initialize Oracle.register {{")
        lines.append(f'  name := "{name}"')
        lines.append(f"  shape := [{shape_list}]")
        lines.append(
            f"  evalFn := fun coords => evalLayout {name} coords")
        lines.append(f"}}")
        lines.append("")

    lines.append("end LegoLean.Adapter.Generated")
    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# File management
# ---------------------------------------------------------------------------

def update_generated_imports(gen_lean_path: Path, module_name: str) -> None:
    """Add an import line to LegoLean/Generated.lean if not already present."""
    import_line = f"import LegoLean.Adapter.Generated.{module_name}"

    if gen_lean_path.exists():
        content = gen_lean_path.read_text()
        if import_line in content:
            return  # already present
        # Append the import
        if not content.endswith("\n"):
            content += "\n"
        content += import_line + "\n"
        gen_lean_path.write_text(content)
    else:
        gen_lean_path.write_text(
            "-- Auto-generated imports\n" + import_line + "\n")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate Lean 4 source from a JSON layout specification.")
    parser.add_argument(
        "spec", type=str, help="Path to JSON spec file")
    parser.add_argument(
        "--output-dir", type=str, default=None,
        help="Output directory (default: LegoLean/Generated relative to "
             "project root)")
    parser.add_argument(
        "--no-oracle", action="store_true",
        help="Skip oracle registration code")
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Print generated code to stdout instead of writing files")
    parser.add_argument(
        "--project-root", type=str, default=None,
        help="Project root directory (default: auto-detect from script "
             "location)")

    args = parser.parse_args()

    # Determine project root
    if args.project_root:
        project_root = Path(args.project_root)
    else:
        # Script is in tools/, project root is one level up
        project_root = Path(__file__).resolve().parent.parent

    # Read and validate spec
    spec_path = Path(args.spec)
    if not spec_path.exists():
        print(f"Error: spec file not found: {spec_path}", file=sys.stderr)
        sys.exit(1)

    with open(spec_path) as f:
        spec = json.load(f)

    try:
        validate_spec(spec)
    except ValueError as e:
        print(f"Validation error: {e}", file=sys.stderr)
        sys.exit(1)

    # Generate Lean source
    lean_src = generate_lean(spec, include_oracle=not args.no_oracle)

    if args.dry_run:
        print(lean_src)
        return

    # Determine output paths
    name = spec["name"]
    module_name = name_to_module(name)

    if args.output_dir:
        output_dir = Path(args.output_dir)
    else:
        output_dir = project_root / "LegoLean" / "Adapter" / "Generated"

    output_dir.mkdir(parents=True, exist_ok=True)
    output_file = output_dir / f"{module_name}.lean"
    output_file.write_text(lean_src)
    print(f"Generated: {output_file}")

    # Update Generated.lean imports
    gen_lean = project_root / "LegoLean" / "Adapter" / "Generated.lean"
    update_generated_imports(gen_lean, module_name)
    print(f"Updated:   {gen_lean}")


if __name__ == "__main__":
    main()
