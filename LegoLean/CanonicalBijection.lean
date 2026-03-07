/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Canonical Bijection B

This file defines the canonical bijection B between multi-dimensional indices
and flat indices, corresponding to the row-major linearization:

  B(n₁,...,nq)(i₁,...,iq) = i₁ · (n₂·...·nq) + i₂ · (n₃·...·nq) + ... + iq

The key insight is that Mathlib's `finPiFinEquiv` is exactly this bijection.

## References
- LEGO paper, Section III-B, Equations for B and B⁻¹
- Python source: `flatten_index()`, `unflatten_index()`
-/

import LegoLean.Basic

namespace LegoLean

/-- The canonical bijection B from multi-indices to flat indices.
    This is the row-major linearization:
      B(n₁,...,nq)(i₁,...,iq) = i₁·(n₂·...·nq) + ... + iq

    We use Mathlib's `finPiFinEquiv` which provides exactly this bijection
    together with its inverse, bundled as an `Equiv`.

    Note: `finPiFinEquiv` has type `(∀ i : Fin d, Fin (s i)) ≃ Fin (∏ i, s i)`,
    which is exactly `MultiIndex s ≃ FlatIndex s` after unfolding definitions. -/
noncomputable def B {d : ℕ} (s : Shape d) : MultiIndex s ≃ FlatIndex s :=
  (finPiFinEquiv : ((i : Fin d) → Fin (s i)) ≃ Fin (∏ i : Fin d, s i))

/-- B⁻¹ is simply the inverse of B, extracting multi-dimensional coordinates
    from a flat index via iterated division and modulo.
    B⁻¹(n₁,...,nq)(j) = (j / (n₂·...·nq), ..., j mod nq) -/
noncomputable def Binv {d : ℕ} (s : Shape d) : FlatIndex s ≃ MultiIndex s :=
  (B s).symm

/-- B composed with B⁻¹ is the identity on flat indices. -/
theorem B_Binv {d : ℕ} (s : Shape d) :
    (B s) ∘ (Binv s) = id :=
  funext (fun x => (B s).apply_symm_apply x)

/-- B⁻¹ composed with B is the identity on multi-indices. -/
theorem Binv_B {d : ℕ} (s : Shape d) :
    (Binv s) ∘ (B s) = id :=
  funext (fun x => (B s).symm_apply_apply x)

/-- B is a bijection (automatic from Equiv). -/
theorem B_bijective {d : ℕ} (s : Shape d) :
    Function.Bijective (B s) :=
  (B s).bijective

/-- B⁻¹ is a bijection (automatic from Equiv). -/
theorem Binv_bijective {d : ℕ} (s : Shape d) :
    Function.Bijective (Binv s) :=
  (Binv s).bijective

/-- Bridge lemma: B equals finPiFinEquiv (by definition). -/
theorem B_eq_finPiFinEquiv {d : ℕ} (s : Shape d) :
    (B s) = (finPiFinEquiv : ((i : Fin d) → Fin (s i)) ≃ Fin (∏ i : Fin d, s i)) := rfl

end LegoLean
