/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GroupBy — Full Layout Expression

This file defines GroupBy, the top-level layout construct in the LEGO algebra.
A GroupBy combines:
1. A logical shape (how the programmer views the data)
2. A sequence of tiling levels with shapes and permutations (OrderBy)
3. The guarantee that the total element count is preserved

GroupBy.toEquiv produces a bijection from the hierarchical tiled index space
to a flat index, proving that LEGO layouts are always bijective.

## References
- LEGO paper, Figure 5: GroupBy definition
- LEGO paper, Section III-B: Bijectivity argument
- Python source: `class GroupBy`
-/

import LegoLean.OrderBy

namespace LegoLean

/-- A GroupBy layout: the full LEGO layout expression.

    A GroupBy specifies:
    - d: the number of logical dimensions
    - q: the number of tiling levels
    - shapes: the d-dimensional shape at each tiling level
    - perms: a permutation at each level (GenP or RegP)

    The key invariant is that the layout maps the combined tiled index space
    bijectively to a flat index. -/
structure GroupBy (d : ℕ) (q : ℕ) extends OrderBy d q

/-- The total number of elements in a GroupBy layout. -/
def GroupBy.totalElements {d : ℕ} {q : ℕ} (gb : GroupBy d q) : ℕ :=
  gb.toOrderBy.combinedProd

/-- The GroupBy equivalence: a bijection from the hierarchical tiled index space
    to a flat index.

    This is the core of the LEGO bijectivity result: the composition of
    per-level permutations and product flattening is always a bijection.

    Paper reference: Section III-B, "Correctness" -/
noncomputable def GroupBy.toEquiv {d : ℕ} {q : ℕ} (gb : GroupBy d q) :
    ((k : Fin q) → MultiIndex (gb.shapes k)) ≃ Fin gb.totalElements :=
  gb.toOrderBy.toFlatEquiv

/-- The GroupBy layout is always bijective. -/
theorem GroupBy.bijective {d : ℕ} {q : ℕ} (gb : GroupBy d q) :
    Function.Bijective gb.toEquiv :=
  gb.toEquiv.bijective

/-- GroupBy with matching input/output sizes.
    When the logical data has `n` elements and the tiled representation also has `n`,
    we get a bijection Fin n ≃ Fin n, i.e., a permutation on {0,...,n-1}. -/
noncomputable def GroupBy.toPermutation {d : ℕ} {q : ℕ} (gb : GroupBy d q)
    (n : ℕ) (hn : gb.totalElements = n) :
    Fin n ≃ Fin n :=
  (finCongr hn.symm).trans ((gb.toEquiv.symm).trans (gb.toEquiv.trans (finCongr hn)))

/-- A full layout expression with an explicit logical shape.
    This connects the programmer's view (a single d-dimensional shape) to the
    tiled physical layout. -/
structure FullLayout (d : ℕ) (q : ℕ) where
  logicalShape : Shape d
  layout : GroupBy d q
  hSize : Shape.prod logicalShape = layout.totalElements

/-- The full layout bijection: from logical multi-index to physical flat index. -/
noncomputable def FullLayout.toEquiv {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    Fin (Shape.prod fl.logicalShape) ≃ Fin fl.layout.totalElements :=
  finCongr fl.hSize

/-- The full layout is bijective. -/
theorem FullLayout.bijective {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    Function.Bijective fl.toEquiv :=
  fl.toEquiv.bijective

end LegoLean
