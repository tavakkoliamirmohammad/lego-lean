/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# OrderBy — Permutation Chain

This file defines OrderBy, which composes multiple tile-level permutations
across a hierarchy of tiling levels. Given q tiling levels each with d dimensions,
OrderBy applies a permutation at each level, accumulating the flat index.

Apply traverses outermost→innermost:
  for each level k from 0 to q-1:
    extract d-dim sub-index for level k
    apply that level's permutation → flat tile index
    accumulate: total = total * tileSize(k) + flatTileIndex

Inv traverses innermost→outermost:
  for each level k from q-1 to 0:
    extract: flatTileIndex = total % tileSize(k); total = total / tileSize(k)
    apply inverse permutation → d-dim sub-index

## References
- LEGO paper, Figure 4: OrderBy definition
- Python source: `class OrderBy`
-/

import LegoLean.Permutation

namespace LegoLean

/-- An OrderBy configuration: q tiling levels, each with d dimensions and a permutation.
    - `shapes k` gives the d-dimensional shape at tiling level k
    - `perms k` gives the permutation to apply at level k -/
structure OrderBy (d : ℕ) (q : ℕ) where
  shapes : Fin q → Shape d
  perms : (k : Fin q) → TilePerm d (shapes k)

/-- The combined shape of an OrderBy as a (q * d)-dimensional shape.
    The dimensions are organized as: level 0 dims, level 1 dims, ..., level (q-1) dims.

    For the purpose of defining the bijection, we view the combined index space as
    (k : Fin q) × (i : Fin d) → Fin (shapes k i), which has the same cardinality
    as the product space. -/
def OrderBy.combinedProd {d : ℕ} {q : ℕ} (ob : OrderBy d q) : ℕ :=
  ∏ k : Fin q, Shape.prod (ob.shapes k)

/-- The equivalence at a single tiling level. -/
noncomputable def OrderBy.levelEquiv {d : ℕ} {q : ℕ} (ob : OrderBy d q) (k : Fin q) :
    MultiIndex (ob.shapes k) ≃ FlatIndex (ob.shapes k) :=
  (ob.perms k).toEquiv

/-- An OrderBy with q levels defines a bijection on the combined index space.

    The combined index space is:
      (k : Fin q) → Fin (Shape.prod (shapes k))

    which has ∏ k, Shape.prod (shapes k) elements.

    The OrderBy applies each level's permutation independently, yielding a
    per-level flat index, then combines them via the product structure.

    This is equivalent to applying each level's perm independently and
    then using the product structure — which is exactly `Equiv.piCongrRight`. -/
noncomputable def OrderBy.toEquiv {d : ℕ} {q : ℕ} (ob : OrderBy d q) :
    ((k : Fin q) → MultiIndex (ob.shapes k)) ≃
    ((k : Fin q) → FlatIndex (ob.shapes k)) :=
  Equiv.piCongrRight (fun k => ob.levelEquiv k)

/-- The flattened OrderBy equivalence: from the product of multi-indices
    to a single flat index.

    Composes:
    1. Per-level permutations (OrderBy.toEquiv)
    2. Product flattening (finPiFinEquiv on the per-level products) -/
noncomputable def OrderBy.toFlatEquiv {d : ℕ} {q : ℕ} (ob : OrderBy d q) :
    ((k : Fin q) → MultiIndex (ob.shapes k)) ≃ Fin ob.combinedProd :=
  ob.toEquiv.trans (finPiFinEquiv (n := fun k => Shape.prod (ob.shapes k)))

end LegoLean
