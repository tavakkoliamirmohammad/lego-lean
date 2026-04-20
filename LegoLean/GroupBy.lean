/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GroupBy — Full Layout Expression

This file defines GroupBy, the top-level layout construct in the LEGO algebra.
A GroupBy combines:
1. Tile shapes at each tiling level
2. A composed flat permutation (can be built from any number of OrderBy chains)
3. The guarantee that the layout is always bijective

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
    - perm: a composed flat permutation on the product space

    The key invariant is that the layout maps the combined tiled index space
    bijectively to a flat index.

    This design supports multiple OrderBy chains with different dimensionalities,
    matching the paper's GroupBy(tiles, O₁, O₂, ...) construct. -/
structure GroupBy (d : ℕ) (q : ℕ) where
  shapes : Fin q → Shape d
  perm : Fin (∏ k : Fin q, Shape.prod (shapes k)) ≃
         Fin (∏ k : Fin q, Shape.prod (shapes k))

/-- The total number of elements in a GroupBy layout. -/
def GroupBy.totalElements {d q : ℕ} (gb : GroupBy d q) : ℕ :=
  ∏ k : Fin q, Shape.prod (gb.shapes k)

/-- The GroupBy equivalence: a bijection from the hierarchical tiled index space
    to a flat index.

    Composes plain flattening (B at each level + product) with the composed
    flat permutation.

    Paper reference: Section III-B, "Correctness" -/
def GroupBy.toEquiv {d q : ℕ} (gb : GroupBy d q) :
    ((k : Fin q) → MultiIndex (gb.shapes k)) ≃ Fin gb.totalElements :=
  (plainFlatten gb.shapes).trans gb.perm

/-- The GroupBy layout is always bijective. -/
theorem GroupBy.bijective {d q : ℕ} (gb : GroupBy d q) :
    Function.Bijective gb.toEquiv :=
  gb.toEquiv.bijective

/-- Smart constructor: build a GroupBy from a single OrderBy chain (most common). -/
def GroupBy.ofOrderBy {d q : ℕ} (ob : OrderBy d q) : GroupBy d q :=
  { shapes := ob.shapes, perm := ob.asFlatPerm }

/-- Smart constructor: identity layout (no reordering, just standard tiling). -/
def GroupBy.identity {d q : ℕ} (shapes : Fin q → Shape d) : GroupBy d q :=
  { shapes := shapes, perm := Equiv.refl _ }

/-- Smart constructor: compose an additional flat permutation onto a GroupBy. -/
def GroupBy.compose {d q : ℕ} (gb : GroupBy d q)
    (extraPerm : Fin gb.totalElements ≃ Fin gb.totalElements) : GroupBy d q :=
  { shapes := gb.shapes, perm := gb.perm.trans extraPerm }

/-- Smart constructor: build from two OrderBy chains with different d/q (cross-dimensional).
    Paper's GroupBy(tiles, O₁, O₂) = apply O₂ then O₁ (reverse composition order). -/
def GroupBy.ofTwoChains {d q d₁ q₁ d₂ q₂ : ℕ}
    (shapes : Fin q → Shape d)
    (ob₁ : OrderBy d₁ q₁) (ob₂ : OrderBy d₂ q₂)
    (h₁ : ob₁.combinedProd = ∏ k : Fin q, Shape.prod (shapes k))
    (h₂ : ob₂.combinedProd = ∏ k : Fin q, Shape.prod (shapes k)) :
    GroupBy d q :=
  { shapes := shapes
    perm := (ob₂.asFlatPermCast _ h₂).trans (ob₁.asFlatPermCast _ h₁) }

/-! ## Interleaving Permutation σ_{d×q}

The paper's σ_{d×q} = flatten(A) where A : [d][q]int, A_{k,h} = k + 1 + d·h (1-indexed).
In 0-indexed terms: σ(k·q + h) = k + d·h.

This is the matrix transpose on a d×q grid: decompose a flat index as (row, col)
in a d×q matrix, then re-flatten in column-major order.

In `groupDecomp`, this appears structurally as `Equiv.piComm`, which swaps
the order of dependent function arguments from (dim, level) to (level, dim). -/

/-- The interleaving permutation σ_{d×q} from the LEGO paper.
    Maps σ(k·q + h) = k + d·h (0-indexed), equivalently transposing a d×q matrix.

    Paper reference: σ_{d×q} = flatten(A), A_{k,h} = k + 1 + d·h (1-indexed) -/
def sigmaPerm (d q : ℕ) : Fin (d * q) ≃ Fin (d * q) :=
  finProdFinEquiv.symm
  |>.trans (Equiv.prodComm (Fin d) (Fin q))
  |>.trans finProdFinEquiv
  |>.trans (finCongr (Nat.mul_comm q d))

/-- Per-dimension tiling implies total size equality. -/
theorem tiling_implies_size {d q : ℕ} {shapes : Fin q → Shape d} {logicalShape : Shape d}
    (hTiling : ∀ i, ∏ k : Fin q, shapes k i = logicalShape i) :
    Shape.prod logicalShape = ∏ k : Fin q, Shape.prod (shapes k) := by
  simpa only [Shape.prod, ← hTiling] using Finset.prod_comm

/-- The group decomposition: decomposes a logical multi-index into per-level sub-indices.
    MultiIndex logicalShape ≃ (k : Fin q) → MultiIndex (shapes k) -/
def groupDecomp {d q : ℕ} (logicalShape : Shape d) (shapes : Fin q → Shape d)
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
def FullLayout.toEquiv {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    MultiIndex fl.logicalShape ≃ Fin fl.layout.totalElements :=
  (groupDecomp fl.logicalShape fl.layout.shapes fl.hTiling).trans fl.layout.toEquiv

/-- The full layout is bijective. -/
theorem FullLayout.bijective {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    Function.Bijective fl.toEquiv :=
  fl.toEquiv.bijective

/-- The full layout as a permutation on Fin n (when sizes match). -/
def FullLayout.toPermutation {d : ℕ} {q : ℕ} (fl : FullLayout d q) :
    Fin (Shape.prod fl.logicalShape) ≃ Fin fl.layout.totalElements :=
  (B fl.logicalShape).symm.trans fl.toEquiv

/-- TileBy: the primary user-facing LEGO tiling construct.
    Specifies d-dimensional tile shapes at q levels, each with a permutation.
    Generates a bijective GroupBy layout.

    Corresponds to Python's `TileBy(*group_dims)`.

    Paper reference: LEGO paper, Section III-B -/
structure TileBy (d : ℕ) (q : ℕ) where
  shapes : Fin q → Shape d
  perms : (k : Fin q) → TilePerm d (shapes k)

namespace TileBy

/-- The underlying OrderBy. -/
def toOrderBy {d q : ℕ} (tb : TileBy d q) : OrderBy d q :=
  ⟨tb.shapes, tb.perms⟩

/-- Convert to GroupBy. -/
def toGroupBy {d q : ℕ} (tb : TileBy d q) : GroupBy d q :=
  GroupBy.ofOrderBy tb.toOrderBy

/-- Total number of elements in the tiled space. -/
def totalElements {d q : ℕ} (tb : TileBy d q) : ℕ :=
  tb.toGroupBy.totalElements

/-- The TileBy equivalence: hierarchical tiled indices → flat index. -/
def toEquiv {d q : ℕ} (tb : TileBy d q) :
    ((k : Fin q) → MultiIndex (tb.shapes k)) ≃ Fin tb.totalElements :=
  tb.toGroupBy.toEquiv

/-- TileBy is always bijective. -/
theorem bijective {d q : ℕ} (tb : TileBy d q) :
    Function.Bijective tb.toEquiv :=
  tb.toEquiv.bijective

/-- TileBy is injective. -/
theorem injective {d q : ℕ} (tb : TileBy d q) :
    Function.Injective tb.toEquiv :=
  tb.toEquiv.injective

/-- TileBy is surjective. -/
theorem surjective {d q : ℕ} (tb : TileBy d q) :
    Function.Surjective tb.toEquiv :=
  tb.toEquiv.surjective

/-- Create a FullLayout from a TileBy and a logical shape. -/
def toFullLayout {d q : ℕ} (tb : TileBy d q) (logicalShape : Shape d)
    (hTiling : ∀ i, ∏ k : Fin q, tb.shapes k i = logicalShape i) : FullLayout d q :=
  ⟨logicalShape, tb.toGroupBy, hTiling⟩

/-- The FullLayout from TileBy is bijective. -/
theorem fullLayout_bijective {d q : ℕ} (tb : TileBy d q) (logicalShape : Shape d)
    (hTiling : ∀ i, ∏ k : Fin q, tb.shapes k i = logicalShape i) :
    Function.Bijective (tb.toFullLayout logicalShape hTiling).toEquiv :=
  (tb.toFullLayout logicalShape hTiling).bijective

end TileBy

end LegoLean
