# LEGO-Lean — Formal Verification of the LEGO Layout Algebra in Lean 4

Lean 4 formalization of the **LEGO Layout Algebra** from the CGO 2026 paper:

> **LEGO: A Layout Expression Language for Code Generation of Hierarchical Mapping**
> [https://arxiv.org/pdf/2505.08091](https://arxiv.org/pdf/2505.08091)

This project proves that every layout transformation constructed by the LEGO algebra is **bijective by construction**, using Mathlib's `Equiv` type to enforce invertibility at every composition step. All proofs are complete with zero `sorry`.

## Overview

The LEGO algebra maps logical multi-dimensional indices to physical flat memory addresses on GPUs. The key correctness property is that these mappings are always bijections — no two logical indices collide, and every physical address is reachable.

### Formalized constructs

| Paper construct | Lean definition | File |
|---|---|---|
| Shape, MultiIndex | `Shape`, `MultiIndex` | `Basic.lean` |
| Canonical bijection B | `B` (via `finPiFinEquiv`) | `Basic.lean` |
| GenP (general permutation) | `GenP`, `TilePerm.genP` | `Permutation.lean` |
| RegP (dimension permutation) | `RegP`, `TilePerm.regP` | `Permutation.lean` |
| OrderBy (permutation chain) | `OrderBy.toFlatEquiv` | `OrderBy.lean` |
| GroupBy (full layout) | `GroupBy.toEquiv` | `GroupBy.lean` |
| Group decomposition | `groupDecomp` | `GroupBy.lean` |
| FullLayout (logical shape + tiling) | `FullLayout.toEquiv` | `GroupBy.lean` |
| ExpandBy (partial tiles) | `ExpandBy.apply` | `ExpandBy.lean` |
| Table II simplification rules | `rule1`..`rule7` | `Simplification.lean` |
| Main bijectivity theorem | `lego_bijectivity` | `MainTheorem.lean` |

### File structure

```
LegoLean/
  Basic.lean             -- Shape, MultiIndex, FlatIndex, canonical bijection B
  Permutation.lean       -- GenP, RegP, TilePerm
  OrderBy.lean           -- Per-level permutation chain
  GroupBy.lean            -- GroupBy, groupDecomp, FullLayout
  ExpandBy.lean           -- Partial tile support with bounds checking
  Simplification.lean    -- 7 simplification rules (Table II)
  MainTheorem.lean       -- Main bijectivity theorem and corollaries
  Examples.lean          -- Concrete examples (6x4, 6x6 with antidiagonal)
  AntiDiagonal.lean      -- Antidiagonal GenP example
```

## Build

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)

The Lean toolchain version is pinned in `lean-toolchain` and installed automatically by `elan`.

### Build and verify

```bash
# Clone the repository
git clone https://github.com/tavakkoliamirmohammad/lego-lean.git && cd lego-lean

# Download Mathlib cache (speeds up build significantly)
lake exe cache get

# Build all files and check all proofs
lake build
```

A successful build with zero errors means all proofs are verified by the Lean kernel.
