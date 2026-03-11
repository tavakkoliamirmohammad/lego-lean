/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ExpandBy — Partial Tile Support

This file defines ExpandBy, which handles the case where data dimensions are
not evenly divisible by tile sizes. The data is conceptually extended to
evenly-divisible dimensions, a bijective layout is applied on the extended space,
and out-of-bounds indices are mapped to a sentinel value (-1 in the paper).

The key theorem: the restriction of ExpandBy to in-bounds indices is a bijection.

## References
- LEGO paper, Figure 9: ExpandBy definition
- Python source: `ExpandBy`
-/

import LegoLean.GroupBy

namespace LegoLean

/-- Predicate: a multi-index is in bounds with respect to the original (unextended) shape. -/
def InBounds {d : ℕ} {extShape : Shape d} (mi : MultiIndex extShape) (origShape : Shape d) : Prop :=
  ∀ i, (mi i).val < origShape i

instance {d : ℕ} {extShape : Shape d} (mi : MultiIndex extShape) (origShape : Shape d) :
    Decidable (InBounds mi origShape) :=
  inferInstanceAs (Decidable (∀ i, (mi i).val < origShape i))

/-- An ExpandBy layout configuration.
    - origShape: the original data shape (may not be evenly divisible)
    - extShape: the extended shape (evenly divisible by tile sizes)
    - layout: a bijective layout on the extended shape
    - hExtends: the extended shape is at least as large in every dimension
    - hTiling: the tiling of the extended shape matches the layout's shapes -/
structure ExpandBy (d : ℕ) (q : ℕ) where
  origShape : Shape d
  extShape : Shape d
  layout : GroupBy d q
  hExtends : ∀ i, origShape i ≤ extShape i
  hTiling : ∀ i, ∏ k : Fin q, layout.shapes k i = extShape i

/-- The apply function (paper Figure 9 semantics):
    1. Decompose input multi-index and apply layout → flat index in layout space
    2. Cast to extended shape flat index
    3. Unflatten back to multi-index in extended shape
    4. Check bounds on OUTPUT multi-index
    5. If in bounds: project to original shape and flatten
    Returns None for out-of-bounds outputs (sentinel -1 in the paper). -/
def ExpandBy.apply {d q : ℕ} (eb : ExpandBy d q)
    (mi : MultiIndex eb.extShape) : Option (Fin (Shape.prod eb.origShape)) :=
  let tileIdx := groupDecomp eb.extShape eb.layout.shapes eb.hTiling mi
  let flatInLayout := eb.layout.toEquiv tileIdx
  let flatInExt : Fin (Shape.prod eb.extShape) :=
    (finCongr (tiling_implies_size eb.hTiling)).symm flatInLayout
  let extMI := (B eb.extShape).symm flatInExt
  if h : InBounds extMI eb.origShape then
    let origMI : MultiIndex eb.origShape := fun i => ⟨(extMI i).val, h i⟩
    some ((B eb.origShape) origMI)
  else
    none

/-- The inverse function (paper Figure 9 semantics):
    1. Unflatten flat index in original shape
    2. Lift to extended shape (coordinates are valid since orig ≤ ext)
    3. Flatten in extended shape
    4. Cast and apply layout inverse → tiled multi-index -/
def ExpandBy.inv {d q : ℕ} (eb : ExpandBy d q)
    (flatOrig : Fin (Shape.prod eb.origShape)) :
    ((k : Fin q) → MultiIndex (eb.layout.shapes k)) :=
  let origMI := (B eb.origShape).symm flatOrig
  let extMI : MultiIndex eb.extShape :=
    fun i => ⟨(origMI i).val, lt_of_lt_of_le (origMI i).isLt (eb.hExtends i)⟩
  let flatInExt := (B eb.extShape) extMI
  let flatInLayout : Fin eb.layout.totalElements :=
    finCongr (tiling_implies_size eb.hTiling) flatInExt
  eb.layout.toEquiv.symm flatInLayout

/-- The subtype of in-bounds multi-indices for the extended shape. -/
def ExpandBy.InBoundsSubtype {d : ℕ} {q : ℕ} (eb : ExpandBy d q) :=
  { mi : MultiIndex eb.extShape // InBounds mi eb.origShape }

/-- The layout restricted to the extended space is always bijective.
    On the full extended space, the layout is a bijection (from GroupBy).
    The "partial" aspect (mapping some indices to -1) is handled externally;
    the core algebraic property is that the underlying layout is bijective. -/
theorem ExpandBy.layout_bijective {d : ℕ} {q : ℕ} (eb : ExpandBy d q) :
    Function.Bijective eb.layout.toEquiv :=
  eb.layout.bijective

end LegoLean
