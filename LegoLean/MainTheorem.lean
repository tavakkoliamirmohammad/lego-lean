/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Main Bijectivity Theorem

This file states and proves the main theorem of the LEGO layout algebra
formalization: every layout expression constructed using the LEGO algebra
(GenP, RegP, OrderBy, GroupBy) produces a bijective mapping.

The proof is essentially trivial once all constructs are built using Equiv:
the Lean type system enforces bijectivity at every composition step.
The value is that the entire construction type-checks.

## References
- LEGO paper, Section III-B: "Correctness"
- LEGO paper, Theorem: "The LEGO algebra produces bijective layouts"
-/

import LegoLean.GroupBy
import LegoLean.ExpandBy

namespace LegoLean

/-- **Main Theorem (LEGO Bijectivity):**
    Given any LEGO layout expression constructed as a GroupBy with d dimensions
    and q tiling levels, the resulting mapping from the hierarchical tiled index
    space to the flat index space is a bijection.

    This theorem captures the central correctness claim of the LEGO paper
    (Section III-B): the algebra of layout transformations is provably bijective
    by construction. Every GenP provides a user-certified bijection, every RegP
    is a dimension permutation composed with the canonical bijection B, and
    every composition via OrderBy/GroupBy preserves bijectivity through
    Equiv.trans.

    Paper reference: Section III-B, "Correctness" -/
theorem lego_bijectivity (d q : ℕ) (gb : GroupBy d q) :
    Function.Bijective gb.toEquiv :=
  gb.toEquiv.bijective

/-- **Corollary: LEGO layouts are injective.**
    No two distinct multi-indices map to the same flat index. -/
theorem lego_injective (d q : ℕ) (gb : GroupBy d q) :
    Function.Injective gb.toEquiv :=
  gb.toEquiv.injective

/-- **Corollary: LEGO layouts are surjective.**
    Every flat index is the image of some multi-index. -/
theorem lego_surjective (d q : ℕ) (gb : GroupBy d q) :
    Function.Surjective gb.toEquiv :=
  gb.toEquiv.surjective

/-- **Corollary: LEGO layouts have computable inverses.**
    The inverse mapping (from flat index back to multi-index) exists and
    round-trips correctly. -/
theorem lego_inverse_roundtrip (d q : ℕ) (gb : GroupBy d q)
    (mi : (k : Fin q) → MultiIndex (gb.shapes k)) :
    gb.toEquiv.symm (gb.toEquiv mi) = mi :=
  gb.toEquiv.symm_apply_apply mi

/-- **Corollary: LEGO layouts preserve element count.**
    The number of multi-indices equals the number of flat indices. -/
theorem lego_card_eq (d q : ℕ) (gb : GroupBy d q) :
    Fintype.card ((k : Fin q) → MultiIndex (gb.shapes k)) =
    Fintype.card (Fin gb.totalElements) := by
  exact Fintype.card_congr gb.toEquiv

/-- **ExpandBy preserves bijectivity on the extended space.**
    When partial tiles are used, the underlying layout on the extended
    (evenly-divisible) space is still bijective. -/
theorem lego_expandby_bijectivity (d q : ℕ) (eb : ExpandBy d q) :
    Function.Bijective eb.layout.toEquiv :=
  eb.layout_bijective

/-- **FullLayout bijectivity:**
    The full layout bijection from logical multi-indices to flat indices
    is bijective. -/
theorem lego_full_layout_bijectivity (d q : ℕ) (fl : FullLayout d q) :
    Function.Bijective fl.toEquiv :=
  fl.bijective

/-- **FullLayout permutation bijectivity:**
    The full layout permutation (Fin n ≃ Fin m) is bijective. -/
theorem lego_full_layout_perm_bijectivity (d q : ℕ) (fl : FullLayout d q) :
    Function.Bijective fl.toPermutation :=
  fl.toPermutation.bijective

end LegoLean
