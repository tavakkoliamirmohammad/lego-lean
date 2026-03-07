/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Antidiagonal GenP

This file defines the antidiagonal permutation as a concrete GenP.
For a 2D shape (n, m), the antidiagonal reverses the column index:
  (i, j) ↦ i * m + (m - 1 - j)

This is the element-reversal permutation used in Figure 6 of the paper.
We construct it as an `Equiv` and prove it is bijective.

## References
- LEGO paper, Figure 6: antidiagonal permutation in 6×6 example
- Python source: antidiagonal GenP
-/

import LegoLean.Permutation
import Mathlib.Tactic.FinCases

namespace LegoLean

/-! ## Column-reversal equivalence on Fin m

The core building block: reversing the index within `Fin m`.
Maps `j ↦ m - 1 - j`. This is self-inverse. -/

/-- Reverse an index in `Fin m`: maps j to m - 1 - j.
    For m > 0, this is the "mirror" or "complement" operation. -/
def Fin.rev {m : ℕ} (j : Fin m) : Fin m :=
  ⟨m - 1 - j.val, by omega⟩

/-- Reversing twice is the identity. -/
theorem Fin.rev_rev {m : ℕ} (j : Fin m) : Fin.rev (Fin.rev j) = j := by
  ext
  simp [Fin.rev]
  omega

/-- The reversal on Fin m as an equivalence (involutive, hence self-inverse). -/
def finRevEquiv {m : ℕ} : Fin m ≃ Fin m where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-! ## Antidiagonal permutation on a 2D shape

For shape (n, m), the antidiagonal maps (i, j) to (i, m-1-j),
i.e., it reverses the column index while keeping the row. -/

/-- The antidiagonal multi-index transformation on a 2D shape.
    Maps (i, j) ↦ (i, m-1-j). -/
def antiDiagMultiIndex {s : Shape 2} (mi : MultiIndex s) : MultiIndex s :=
  fun k =>
    match k with
    | ⟨0, _⟩ => mi ⟨0, by omega⟩
    | ⟨1, _⟩ => Fin.rev (mi ⟨1, by omega⟩)

/-- Applying the antidiagonal transformation twice is the identity. -/
theorem antiDiagMultiIndex_involutive {s : Shape 2} (mi : MultiIndex s) :
    antiDiagMultiIndex (antiDiagMultiIndex mi) = mi := by
  funext k
  fin_cases k <;> simp [antiDiagMultiIndex, Fin.rev_rev]

/-- The antidiagonal multi-index transformation as an equivalence on MultiIndex s.
    Self-inverse since reversing columns twice is identity. -/
def antiDiagMultiIndexEquiv (s : Shape 2) : MultiIndex s ≃ MultiIndex s where
  toFun := antiDiagMultiIndex
  invFun := antiDiagMultiIndex
  left_inv := antiDiagMultiIndex_involutive
  right_inv := antiDiagMultiIndex_involutive

/-- The antidiagonal GenP: composes column-reversal with the canonical bijection B.
    Maps (i, j) ↦ B(n, m)(i, m-1-j) = i * m + (m - 1 - j).

    This is a concrete `Equiv` from `MultiIndex s` to `FlatIndex s`. -/
noncomputable def antiDiagGenP (s : Shape 2) : MultiIndex s ≃ FlatIndex s :=
  (antiDiagMultiIndexEquiv s).trans (B s)

/-- Wrapping antiDiagGenP as a TilePerm for use in OrderBy/GroupBy. -/
noncomputable def antiDiagTilePerm (s : Shape 2) : TilePerm 2 s :=
  TilePerm.genP (antiDiagGenP s)

/-! ## Concrete verification: 3×3 example

For a 3×3 matrix, the antidiagonal maps:
  (0,0)↦2  (0,1)↦1  (0,2)↦0
  (1,0)↦5  (1,1)↦4  (1,2)↦3
  (2,0)↦8  (2,1)↦7  (2,2)↦6

i.e., each row is reversed. -/

/-- 3×3 shape. -/
def shape3x3 : Shape 2 := ![3, 3]

/-- The antidiagonal is self-inverse: applying it twice gives back the original. -/
example : ∀ mi : MultiIndex shape3x3,
    antiDiagMultiIndex (antiDiagMultiIndex mi) = mi :=
  antiDiagMultiIndex_involutive

/-- Column reversal on Fin 3: rev(2) = 0. -/
example : Fin.rev (⟨2, by omega⟩ : Fin 3) = ⟨0, by omega⟩ := by
  ext; simp [Fin.rev]

/-- Column reversal on Fin 3: rev(0) = 2. -/
example : Fin.rev (⟨0, by omega⟩ : Fin 3) = ⟨2, by omega⟩ := by
  ext; simp [Fin.rev]

/-- Column reversal is self-inverse on Fin 3: rev(rev(1)) = 1. -/
example : Fin.rev (Fin.rev (⟨1, by omega⟩ : Fin 3)) = ⟨1, by omega⟩ := by
  ext; simp [Fin.rev]

end LegoLean
