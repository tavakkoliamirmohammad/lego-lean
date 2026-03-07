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

/-- Per-dimension tiling implies total size equality. -/
theorem tiling_implies_size {d q : ℕ} {shapes : Fin q → Shape d} {logicalShape : Shape d}
    (hTiling : ∀ i, ∏ k : Fin q, shapes k i = logicalShape i) :
    Shape.prod logicalShape = ∏ k : Fin q, Shape.prod (shapes k) := by
  simp only [Shape.prod]
  calc ∏ i : Fin d, logicalShape i
      = ∏ i : Fin d, ∏ k : Fin q, shapes k i := by congr 1; ext i; exact (hTiling i).symm
    _ = ∏ k : Fin q, ∏ i : Fin d, shapes k i := Finset.prod_comm

/-- The group decomposition: decomposes a logical multi-index into per-level sub-indices.
    MultiIndex logicalShape ≃ (k : Fin q) → MultiIndex (shapes k) -/
noncomputable def groupDecomp {d q : ℕ} (logicalShape : Shape d) (shapes : Fin q → Shape d)
    (hTiling : ∀ i, ∏ k : Fin q, shapes k i = logicalShape i) :
    MultiIndex logicalShape ≃ ((k : Fin q) → MultiIndex (shapes k)) :=
  (Equiv.piCongrRight (fun i =>
    (finCongr (hTiling i).symm).trans (finPiFinEquiv (n := fun k => shapes k i)).symm))
  |>.trans (Equiv.piComm (fun i k => Fin (shapes k i)))

/-- A full layout expression with an explicit logical shape.
    This connects the programmer's view (a single d-dimensional shape) to the
    tiled physical layout. -/
structure FullLayout (d : ℕ) (q : ℕ) where
  logicalShape : Shape d
  layout : GroupBy d q
  hTiling : ∀ i, ∏ k : Fin q, layout.shapes k i = logicalShape i

/-- Derived: total size equality. -/
theorem FullLayout.hSize {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    Shape.prod fl.logicalShape = fl.layout.totalElements :=
  tiling_implies_size fl.hTiling

/-- The full layout bijection: logical multi-index → physical flat index.
    Composes: groupDecomp → per-level permutations → flatten. -/
noncomputable def FullLayout.toEquiv {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    MultiIndex fl.logicalShape ≃ Fin fl.layout.totalElements :=
  (groupDecomp fl.logicalShape fl.layout.shapes fl.hTiling).trans fl.layout.toEquiv

/-- The full layout is bijective. -/
theorem FullLayout.bijective {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    Function.Bijective fl.toEquiv :=
  fl.toEquiv.bijective

/-- The full layout as a permutation on Fin n (when sizes match). -/
noncomputable def FullLayout.toPermutation {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    Fin (Shape.prod fl.logicalShape) ≃ Fin fl.layout.totalElements :=
  (B fl.logicalShape).symm.trans fl.toEquiv

end LegoLean
