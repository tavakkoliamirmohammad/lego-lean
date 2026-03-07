/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GenP and RegP — Permutation Constructs

This file defines GenP (general permutation) and RegP (regular/dimension permutation),
the two fundamental permutation constructs in the LEGO algebra.

- **GenP**: Wraps any user-provided bijection MultiIndex s ≃ FlatIndex s.
- **RegP**: Permutes dimensions using σ ∈ Perm(Fin d), then flattens with B.
  RegP(dims, σ)(i) = B(σ(dims))(σ(i))

## References
- LEGO paper, Figure 3: GenP and RegP definitions
- LEGO paper, Figure 4: RegP composition in OrderBy
- Python source: `class GenP`, `class RegP`
-/

import LegoLean.CanonicalBijection

namespace LegoLean

/-- GenP: A general (user-defined) permutation on the index space.
    The user provides any bijection between multi-indices and flat indices.
    Bijectivity is guaranteed by the Equiv type.

    Paper reference: Figure 3, GenP(dims, f, f⁻¹) -/
def GenP {d : ℕ} (s : Shape d) (e : MultiIndex s ≃ FlatIndex s) :
    MultiIndex s ≃ FlatIndex s := e

/-- GenP is always bijective (trivially, since it's an Equiv). -/
theorem GenP_bijective {d : ℕ} (s : Shape d) (e : MultiIndex s ≃ FlatIndex s) :
    Function.Bijective (GenP s e) :=
  e.bijective

/-- Reindex a multi-index by a permutation on dimensions.
    If σ permutes dimensions, then (reindexMultiIndex σ mi) k = mi (σ k).
    This transforms a MultiIndex for shape s into a MultiIndex for shape (s ∘ σ). -/
def reindexMultiIndex {d : ℕ} {s : Shape d} (σ : Equiv.Perm (Fin d))
    (mi : MultiIndex s) : MultiIndex (s ∘ σ) :=
  fun i => mi (σ i)

/-- The reindexing of multi-indices by σ is an equivalence.
    MultiIndex s ≃ MultiIndex (s ∘ σ) -/
noncomputable def reindexEquiv {d : ℕ} (s : Shape d) (σ : Equiv.Perm (Fin d)) :
    MultiIndex s ≃ MultiIndex (s ∘ σ) :=
  Equiv.piCongrLeft' (fun i => Fin (s i)) σ.symm

/-- RegP: Regular (dimension) permutation.
    Permutes the dimensions of a multi-index by σ, then flattens using B.

    RegP(dims, σ)(i₁,...,i_d) = B(dims ∘ σ⁻¹)(i_{σ⁻¹(1)},...,i_{σ⁻¹(d)})

    Constructed as a composition of three equivalences:
    1. Reindex: MultiIndex s ≃ MultiIndex (s ∘ σ⁻¹)   (dimension permutation)
    2. Flatten: MultiIndex (s ∘ σ⁻¹) ≃ FlatIndex (s ∘ σ⁻¹)  (canonical bijection B)
    3. Cast:   FlatIndex (s ∘ σ⁻¹) ≃ FlatIndex s      (products are equal)

    Paper reference: Figure 3, RegP(dims, σ) -/
noncomputable def RegP {d : ℕ} (s : Shape d) (σ : Equiv.Perm (Fin d)) :
    MultiIndex s ≃ FlatIndex s :=
  let σinv := σ.symm
  let permutedShape : Shape d := s ∘ σinv
  -- Step 1: Reindex multi-indices by σ⁻¹
  let step1 : MultiIndex s ≃ MultiIndex permutedShape := reindexEquiv s σinv
  -- Step 2: Flatten using canonical bijection B
  let step2 : MultiIndex permutedShape ≃ FlatIndex permutedShape := B permutedShape
  -- Step 3: Cast flat index (products are equal under permutation)
  let step3 : FlatIndex permutedShape ≃ FlatIndex s :=
    finCongr (Shape.prod_permute s σinv)
  step1.trans (step2.trans step3)

/-- RegP is always bijective (from Equiv composition). -/
theorem RegP_bijective {d : ℕ} (s : Shape d) (σ : Equiv.Perm (Fin d)) :
    Function.Bijective (RegP s σ) :=
  (RegP s σ).bijective

/-- RegP with the identity permutation is equivalent to B. -/
theorem RegP_id {d : ℕ} (s : Shape d) :
    ∀ mi, (RegP s (Equiv.refl (Fin d))) mi = (B s) mi := by
  intro mi
  unfold RegP reindexEquiv B
  simp

/-- A tile permutation is either a GenP or a RegP.
    This corresponds to the P parameter in OrderBy(dims, P₁, ..., Pq). -/
inductive TilePerm (d : ℕ) (s : Shape d) where
  | genP (e : MultiIndex s ≃ FlatIndex s) : TilePerm d s
  | regP (σ : Equiv.Perm (Fin d)) : TilePerm d s

/-- Convert a TilePerm to an equivalence. -/
noncomputable def TilePerm.toEquiv {d : ℕ} {s : Shape d} : TilePerm d s → (MultiIndex s ≃ FlatIndex s)
  | .genP e => GenP s e
  | .regP σ => RegP s σ

/-- Every TilePerm is bijective. -/
theorem TilePerm.bijective {d : ℕ} {s : Shape d} (tp : TilePerm d s) :
    Function.Bijective tp.toEquiv :=
  tp.toEquiv.bijective

end LegoLean
