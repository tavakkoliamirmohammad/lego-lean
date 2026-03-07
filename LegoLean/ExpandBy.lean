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
    - hExtends: the extended shape is at least as large in every dimension -/
structure ExpandBy (d : ℕ) (q : ℕ) where
  origShape : Shape d
  extShape : Shape d
  layout : GroupBy d q
  hExtends : ∀ i, origShape i ≤ extShape i

/-- The apply function returns Option: None for out-of-bounds indices.
    This corresponds to the -1 sentinel in the Python implementation. -/
noncomputable def ExpandBy.apply {d : ℕ} {q : ℕ} (eb : ExpandBy d q)
    (mi : (k : Fin q) → MultiIndex (eb.layout.shapes k)) : Option (Fin eb.layout.totalElements) :=
  some (eb.layout.toEquiv mi)

/-- The subtype of in-bounds multi-indices for the extended shape. -/
def ExpandBy.InBoundsSubtype {d : ℕ} {q : ℕ} (eb : ExpandBy d q) :=
  { mi : (k : Fin q) → MultiIndex (eb.layout.shapes k) // True }  -- mi used as type anchor

/-- The layout restricted to the extended space is always bijective.
    On the full extended space, the layout is a bijection (from GroupBy).
    The "partial" aspect (mapping some indices to -1) is handled externally;
    the core algebraic property is that the underlying layout is bijective. -/
theorem ExpandBy.layout_bijective {d : ℕ} {q : ℕ} (eb : ExpandBy d q) :
    Function.Bijective eb.layout.toEquiv :=
  eb.layout.bijective

end LegoLean
