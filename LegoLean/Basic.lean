/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Basic Definitions for the LEGO Layout Algebra

This file defines the foundational types: Shape, MultiIndex, FlatIndex,
and supporting lemmas. These correspond to the index spaces described in
Section III-B of the LEGO paper (CGO 2026).

## References
- LEGO paper, Section III-B: "Correctness"
- Python source: `lego.py`, `flatten_index()`, `unflatten_index()`
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Perm.Basic

namespace LegoLean

/-- A `Shape d` is a d-dimensional shape, mapping each dimension index to its size.
    Corresponds to the tuple (n₁, n₂, ..., n_d) in the paper. -/
abbrev Shape (d : ℕ) := Fin d → ℕ

/-- A `MultiIndex s` is a bounded multi-dimensional index into a shape `s`.
    Each component `i k` satisfies `0 ≤ i k < s k`.
    Corresponds to (i₁, ..., i_d) where 0 ≤ iₖ < nₖ. -/
abbrev MultiIndex {d : ℕ} (s : Shape d) := (i : Fin d) → Fin (s i)

/-- The total number of elements in a shape: the product of all dimension sizes.
    Corresponds to N = n₁ · n₂ · ... · n_d. -/
def Shape.prod {d : ℕ} (s : Shape d) : ℕ := ∏ i : Fin d, s i

/-- A `FlatIndex s` is a flat (linear) index in `Fin (Shape.prod s)`.
    Ranges over `{0, 1, ..., N-1}` where N = ∏ nₖ. -/
abbrev FlatIndex {d : ℕ} (s : Shape d) := Fin (Shape.prod s)

/-- A shape is positive if all dimension sizes are positive. -/
def Shape.Positive {d : ℕ} (s : Shape d) : Prop := ∀ i, 0 < s i

/-- The product of a positive shape is positive. -/
theorem Shape.prod_pos {d : ℕ} {s : Shape d} (hs : s.Positive) : 0 < s.prod := by
  unfold Shape.prod
  exact Finset.prod_pos (fun i _ => hs i)

/-- Permute a shape by a permutation on dimensions.
    If σ permutes dimensions, then `(Shape.permute s σ) i = s (σ i)`.
    Corresponds to σ(dims) in the paper. -/
def Shape.permute {d : ℕ} (s : Shape d) (σ : Equiv.Perm (Fin d)) : Shape d :=
  s ∘ σ

/-- The product of a permuted shape equals the product of the original shape.
    This is essential: reordering dimensions doesn't change the total element count. -/
theorem Shape.prod_permute {d : ℕ} (s : Shape d) (σ : Equiv.Perm (Fin d)) :
    (s.permute σ).prod = s.prod := by
  unfold Shape.prod Shape.permute
  exact Fintype.prod_equiv σ _ _ (fun i => rfl)

/-- Dimension-reversal equivalence: maps dimension i to dimension d-1-i.
    Used by `B` for row-major ordering and by `col` perm for column-major. -/
def dimRevEquiv (d : ℕ) : Fin d ≃ Fin d where
  toFun i := ⟨d - 1 - i.val, by omega⟩
  invFun i := ⟨d - 1 - i.val, by omega⟩
  left_inv i := by ext; show d - 1 - (d - 1 - i.val) = i.val; omega
  right_inv i := by ext; show d - 1 - (d - 1 - i.val) = i.val; omega

/-- The canonical bijection B from multi-indices to flat indices.
    This is the row-major linearization:
      B(n₁,...,n_d)(i₁,...,i_d) = i₁·(n₂·...·n_d) + ... + i_d

    We compose dimension reversal with `finPiFinEquiv` to achieve row-major
    ordering (most significant index first), since `finPiFinEquiv` natively
    uses little-endian convention (least significant index first). -/
def B {d : ℕ} (s : Shape d) : MultiIndex s ≃ FlatIndex s :=
  (Equiv.piCongrLeft' (fun i => Fin (s i)) (dimRevEquiv d)).trans
    ((finPiFinEquiv (n := fun j => s ((dimRevEquiv d).symm j))).trans
     (finCongr (Shape.prod_permute s (dimRevEquiv d).symm)))

end LegoLean
