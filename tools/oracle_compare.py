#!/usr/bin/env python3
"""
oracle_compare.py — Compare Lean oracle output with an external implementation.

Runs the verified Lean oracle (lake exe oracle) and compares its lookup table
against an external implementation's output, entry by entry.

Usage:
    # Compare oracle with external JSON file
    python tools/oracle_compare.py --layout my_layout --external output.json

    # Compare oracle with external command
    python tools/oracle_compare.py --layout my_layout \
        --external-cmd "python my_impl.py my_layout"

    # Compare two JSON files directly
    python tools/oracle_compare.py --oracle oracle.json --external ext.json

    # Sampled comparison for large layouts
    python tools/oracle_compare.py --layout my_layout --external ext.json \
        --mode sample --samples 1000

The oracle JSON format is:
    {"name": "...", "shape": [...], "table": {"[0,0]": 0, "[0,1]": 1, ...}}
where OOB entries have value null.
"""

import json
import sys
import subprocess
import argparse
import random
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from itertools import product as cartesian_product


def run_oracle(layout_name: str, project_root: Path) -> Dict[str, Any]:
    """Run `lake exe oracle <name>` and parse its JSON output."""
    result = subprocess.run(
        ["lake", "exe", "oracle", layout_name],
        capture_output=True, text=True, cwd=project_root)

    if result.returncode != 0:
        print(f"Oracle failed (exit {result.returncode}):", file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        sys.exit(1)

    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as e:
        print(f"Oracle output is not valid JSON: {e}", file=sys.stderr)
        print(f"Output was: {result.stdout[:500]}", file=sys.stderr)
        sys.exit(1)


def load_json_file(path: str) -> Dict[str, Any]:
    """Load a JSON file."""
    with open(path) as f:
        return json.load(f)


def run_external_cmd(cmd: str) -> Dict[str, Any]:
    """Run an external command and parse its JSON output."""
    result = subprocess.run(
        cmd, shell=True, capture_output=True, text=True)

    if result.returncode != 0:
        print(f"External command failed (exit {result.returncode}):",
              file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        sys.exit(1)

    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as e:
        print(f"External output is not valid JSON: {e}", file=sys.stderr)
        sys.exit(1)


def all_coords(shape: List[int]) -> List[Tuple[int, ...]]:
    """Generate all coordinate tuples for a given shape."""
    return list(cartesian_product(*(range(s) for s in shape)))


def coord_key(coords: Tuple[int, ...]) -> str:
    """Format coordinates as the JSON table key: '[0,1,2]'"""
    return "[" + ",".join(str(c) for c in coords) + "]"


def compare_tables(oracle_data: Dict[str, Any],
                   external_data: Dict[str, Any],
                   mode: str = "exhaustive",
                   num_samples: int = 1000,
                   seed: int = 42
                   ) -> Tuple[int, int, List[str]]:
    """
    Compare two layout lookup tables.

    Returns (total_checked, mismatches, error_messages).
    """
    oracle_table = oracle_data.get("table", {})
    ext_table = external_data.get("table", {})

    # Determine shape — prefer oracle (verified)
    shape = oracle_data.get("shape", external_data.get("shape"))
    if shape is None:
        return 0, 0, ["No shape found in either input"]

    coords = all_coords(shape)

    if mode == "sample" and len(coords) > num_samples:
        rng = random.Random(seed)
        # Always include boundaries + random interior
        boundary_coords = []
        for c in coords:
            if any(x == 0 or x == shape[i] - 1
                   for i, x in enumerate(c)):
                boundary_coords.append(c)

        remaining = [c for c in coords if c not in boundary_coords]
        n_random = max(0, num_samples - len(boundary_coords))
        sampled = boundary_coords + rng.sample(
            remaining, min(n_random, len(remaining)))
        coords = sampled

    total = 0
    mismatches = 0
    errors: List[str] = []

    for c in coords:
        key = coord_key(c)
        oracle_val = oracle_table.get(key)
        ext_val = ext_table.get(key)

        total += 1

        if oracle_val != ext_val:
            mismatches += 1
            errors.append(
                f"  {key}: oracle={oracle_val}, external={ext_val}")
            if mismatches >= 50:
                errors.append(f"  ... (truncated, too many mismatches)")
                break

    return total, mismatches, errors


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compare Lean oracle output with external implementation.")

    # Oracle source (pick one)
    oracle_group = parser.add_mutually_exclusive_group()
    oracle_group.add_argument(
        "--layout", type=str,
        help="Layout name — runs `lake exe oracle <name>`")
    oracle_group.add_argument(
        "--oracle", type=str,
        help="Path to oracle JSON file (skip running lake)")

    # External source (pick one)
    ext_group = parser.add_mutually_exclusive_group(required=True)
    ext_group.add_argument(
        "--external", type=str,
        help="Path to external implementation's JSON file")
    ext_group.add_argument(
        "--external-cmd", type=str,
        help="Command to run external implementation (outputs JSON)")

    parser.add_argument(
        "--mode", choices=["exhaustive", "sample"], default="exhaustive",
        help="Comparison mode (default: exhaustive)")
    parser.add_argument(
        "--samples", type=int, default=1000,
        help="Number of samples for sample mode (default: 1000)")
    parser.add_argument(
        "--seed", type=int, default=42,
        help="Random seed for sample mode (default: 42)")
    parser.add_argument(
        "--project-root", type=str, default=None,
        help="Project root directory (default: auto-detect)")

    args = parser.parse_args()

    # Determine project root
    if args.project_root:
        project_root = Path(args.project_root)
    else:
        project_root = Path(__file__).resolve().parent.parent

    # Get oracle data
    if args.layout:
        print(f"Running oracle for layout '{args.layout}'...")
        oracle_data = run_oracle(args.layout, project_root)
    elif args.oracle:
        oracle_data = load_json_file(args.oracle)
    else:
        print("Error: specify --layout or --oracle", file=sys.stderr)
        sys.exit(1)

    # Get external data
    if args.external:
        external_data = load_json_file(args.external)
    else:
        print(f"Running external command...")
        external_data = run_external_cmd(args.external_cmd)

    # Compare
    oracle_name = oracle_data.get("name", "?")
    ext_name = external_data.get("name", "?")
    print(f"Comparing: oracle='{oracle_name}' vs external='{ext_name}'")

    oracle_shape = oracle_data.get("shape", [])
    ext_shape = external_data.get("shape", [])
    if oracle_shape != ext_shape:
        print(f"WARNING: Shape mismatch! oracle={oracle_shape}, "
              f"external={ext_shape}")

    total_elements = 1
    for s in oracle_shape:
        total_elements *= s

    effective_mode = args.mode
    if effective_mode == "exhaustive" and total_elements > 10000:
        print(f"Shape product = {total_elements} > 10000, "
              f"switching to sample mode ({args.samples} samples)")
        effective_mode = "sample"

    total, mismatches, errors = compare_tables(
        oracle_data, external_data,
        mode=effective_mode,
        num_samples=args.samples,
        seed=args.seed)

    # Report
    print(f"Checked {total} entries, found {mismatches} mismatches")

    if mismatches == 0:
        print("PASS: All entries match!")
        sys.exit(0)
    else:
        print(f"FAIL: {mismatches} mismatches:")
        for err in errors:
            print(err)
        sys.exit(1)


if __name__ == "__main__":
    main()
