/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# TileBy Lowering — Explicit Paper Formula

This file implements the explicit TileBy lowering from the LEGO paper:

  TileBy_{q×d} ≡ GroupBy(P¹_d.dims, ..., Pq_d.dims)
                  . OrderBy(RegP(σ_{d×q}), (P¹_d.dims, ..., Pq_d.dims), σ_{d×q})

where σ_{d×q} = flatten(A), A : [d][q]int, A_{k,h} = k + 1 + d·h (1-indexed).

RegP(dims, σ) in the paper applies σ to both dimensions and multi-indices:
  RegP(dims, σ)(i) = B(σ(dims))(σ(i))

Our Lean `RegP s σ` internally applies σ⁻¹, so to match the paper's
RegP(σ_{d×q}) we pass σ_{d×q}⁻¹ to our Lean `RegP`.

## References
- LEGO paper, Section III-B: TileBy lowering rule
- LEGO paper, Figure 5: σ_{d×q} interleaving permutation
-/

import LegoLean.GroupBy

namespace LegoLean

/-! ## Combined Shape -/

/-- The combined (q·d)-dimensional shape from q d-dimensional tile shapes.
    Organized in level-major order: index p corresponds to level ⌊p/d⌋, dimension p%d.

    For tile shapes s₀, ..., s_{q-1}, the combined shape is:
    (s₀[0], ..., s₀[d-1], s₁[0], ..., s_{q-1}[d-1])

    This is (P¹_d.dims, ..., Pq_d.dims) in the paper. -/
def combinedShape {d q : ℕ} (shapes : Fin q → Shape d) : Shape (q * d) :=
  fun p => shapes (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

/-- The product of the combined shape equals the product of per-level shape products.
    ∏_{p < q·d} combinedShape(p) = ∏_{k < q} ∏_{j < d} shapes[k][j] -/
theorem combinedShape_prod {d q : ℕ} (shapes : Fin q → Shape d) :
    Shape.prod (combinedShape shapes) = ∏ k : Fin q, Shape.prod (shapes k) := by
  unfold Shape.prod combinedShape
  calc ∏ p : Fin (q * d), shapes (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
      = ∏ kj : Fin q × Fin d, shapes kj.1 kj.2 :=
        Fintype.prod_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)
    _ = ∏ k : Fin q, ∏ j : Fin d, shapes k j :=
        Fintype.prod_prod_type' (fun k j => shapes k j)

/-! ## TileBy Lowering -/

namespace TileBy

/-- The combined (q·d)-dimensional shape of a TileBy in level-major order.
    Corresponds to (P¹_d.dims, ..., Pq_d.dims) in the paper. -/
def combined {d q : ℕ} (tb : TileBy d q) : Shape (q * d) :=
  combinedShape tb.shapes

/-- Product of the combined shape equals the TileBy's total elements. -/
theorem combined_prod {d q : ℕ} (tb : TileBy d q) :
    Shape.prod tb.combined = tb.totalElements := by
  unfold combined totalElements toGroupBy GroupBy.totalElements
  exact combinedShape_prod tb.shapes

/-- The lowered OrderBy: a single level with (q·d) dimensions and RegP(σ_{d×q}).

    The paper's RegP(dims, σ)(i) = B(σ(dims))(σ(i)) applies σ directly.
    Our Lean `RegP s σ` applies σ⁻¹ internally, so we pass `(sigmaPerm q d).symm`
    to match the paper's RegP(σ_{d×q}).

    `sigmaPerm q d` on Fin(q·d) maps level-major k·d+j to dimension-major j·q+k,
    implementing the paper's σ_{d×q}.

    Paper reference: OrderBy(RegP(σ_{d×q}), (P¹_d.dims, ..., Pq_d.dims), σ_{d×q}) -/
def loweredOrderBy {d q : ℕ} (tb : TileBy d q) : OrderBy (q * d) 1 where
  shapes := ![tb.combined]
  perms := fun _ => TilePerm.regP (sigmaPerm q d).symm

/-- The lowered OrderBy's combined product equals the TileBy's total elements. -/
theorem loweredOrderBy_combinedProd {d q : ℕ} (tb : TileBy d q) :
    tb.loweredOrderBy.combinedProd = tb.totalElements := by
  unfold loweredOrderBy OrderBy.combinedProd totalElements toGroupBy GroupBy.totalElements
  simp
  exact tb.combined_prod

/-- TileBy lowered to the paper's explicit formula:

    TileBy_{q×d} ≡ GroupBy(P¹_d.dims, ..., Pq_d.dims)
                    . OrderBy(RegP(σ_{d×q}), (P¹_d.dims, ..., Pq_d.dims), σ_{d×q})

    Constructs a GroupBy with the original tile shapes and a flat permutation
    derived from the single (q·d)-dimensional RegP(σ_{d×q}) OrderBy.

    Paper reference: TileBy_{q×d} lowering rule, Section III-B -/
def toLoweredGroupBy {d q : ℕ} (tb : TileBy d q) : GroupBy d q where
  shapes := tb.shapes
  perm := tb.loweredOrderBy.asFlatPermCast tb.totalElements tb.loweredOrderBy_combinedProd

/-- The lowered GroupBy is always bijective. -/
theorem toLoweredGroupBy_bijective {d q : ℕ} (tb : TileBy d q) :
    Function.Bijective tb.toLoweredGroupBy.toEquiv :=
  tb.toLoweredGroupBy.bijective

/-- Create a FullLayout from the lowered TileBy. -/
def toLoweredFullLayout {d q : ℕ} (tb : TileBy d q) (logicalShape : Shape d)
    (hTiling : ∀ i, ∏ k : Fin q, tb.shapes k i = logicalShape i) : FullLayout d q :=
  ⟨logicalShape, tb.toLoweredGroupBy, hTiling⟩

/-- The lowered FullLayout is bijective. -/
theorem toLoweredFullLayout_bijective {d q : ℕ} (tb : TileBy d q) (logicalShape : Shape d)
    (hTiling : ∀ i, ∏ k : Fin q, tb.shapes k i = logicalShape i) :
    Function.Bijective (tb.toLoweredFullLayout logicalShape hTiling).toEquiv :=
  (tb.toLoweredFullLayout logicalShape hTiling).bijective

end TileBy

end LegoLean
