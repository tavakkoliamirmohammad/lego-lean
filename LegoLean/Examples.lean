/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Paper Examples

This file formalizes concrete examples from the LEGO paper as executable checks.
These serve as both documentation and validation that the formalization matches
the paper's intended semantics.

## References
- LEGO paper, Figure 2: 6×4 matrix example
- LEGO paper, Figure 6: 6×6 matrix example
-/

import LegoLean.MainTheorem
import LegoLean.Simplification
import Mathlib.Tactic.FinCases

namespace LegoLean.Examples

/-! ### Example 1: Simple 2D shape

A 6×4 matrix has 24 elements. The canonical bijection B maps
multi-index (i, j) to flat index i * 4 + j (row-major order). -/

/-- Shape (6, 4): a 6×4 matrix. -/
def shape_6x4 : Shape 2 := ![6, 4]

/-- The product of shape (6, 4) is 24. -/
example : Shape.prod shape_6x4 = 24 := by native_decide

/-- Shape (6, 4) is positive. -/
example : shape_6x4.Positive := by
  intro i
  simp only [shape_6x4]
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### Example 2: Shape permutation invariance

Permuting dimensions preserves the product. For (6, 4), swapping
dimensions gives (4, 6), which also has product 24. -/

/-- The swap permutation on 2 dimensions. -/
def swap2 : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) (1 : Fin 2)

/-- Swapping dimensions of (6, 4) gives (4, 6). -/
example : shape_6x4.permute swap2 = ![4, 6] := by
  ext i
  fin_cases i <;> simp [Shape.permute, shape_6x4, swap2, Equiv.swap_apply_left,
    Equiv.swap_apply_right]

/-- The product is invariant: prod(6, 4) = prod(4, 6) = 24. -/
example : (shape_6x4.permute swap2).prod = shape_6x4.prod :=
  Shape.prod_permute shape_6x4 swap2

/-! ### Example 3: Simplification rules in action

Demonstrate that the simplification rules from Table II hold on concrete values. -/

/-- Rule 1 example: (4*3 + 5) % 4 = 5 % 4 = 1 -/
example : (4 * 3 + 5) % 4 = 1 := by native_decide

/-- Rule 2 example: (4*3 + 5) / 4 = 3 + 5/4 = 4 -/
example : (4 * 3 + 5) / 4 = 4 := by native_decide

/-- Rule 3 example: (17 % 4) / 4 = 1 / 4 = 0 -/
example : (17 % 4) / 4 = 0 := by native_decide

/-- Rule 4 example: 3 / 5 = 0 -/
example : 3 / 5 = 0 := by native_decide

/-- Rule 5 example: 3 % 5 = 3 -/
example : 3 % 5 = 3 := by native_decide

/-- Rule 7 example: 4 * (17 / 4) + 17 % 4 = 4 * 4 + 1 = 17 -/
example : 4 * (17 / 4) + 17 % 4 = 17 := by native_decide

/-! ### Example 4: Tiling structure

A 6×4 matrix tiled into 2×2 blocks gives a (3×2)×(2×2) hierarchy.
- Level 0 (blocks): shape (3, 2), product 6
- Level 1 (within block): shape (2, 2), product 4
- Total: 6 * 4 = 24 elements -/

/-- Block-level shape (3, 2). -/
def blockShape : Shape 2 := ![3, 2]

/-- Within-block shape (2, 2). -/
def tileShape : Shape 2 := ![2, 2]

/-- Block level has 6 elements. -/
example : Shape.prod blockShape = 6 := by native_decide

/-- Tile level has 4 elements. -/
example : Shape.prod tileShape = 4 := by native_decide

/-! ### Example 5: GroupBy bijectivity type-check

Construct a concrete GroupBy and verify its bijectivity theorem type-checks.
This is the core demonstration: building a layout and getting bijectivity for free. -/

/-- The shapes for the 2-level tiling, defined separately for computability. -/
def exampleShapes : Fin 2 → Shape 2 := ![blockShape, tileShape]

/-- A concrete OrderBy with 2 levels, each 2-dimensional, using identity permutations. -/
noncomputable def exampleOrderBy : OrderBy 2 2 where
  shapes := exampleShapes
  perms := fun _ => TilePerm.regP (Equiv.refl (Fin 2))

/-- The corresponding GroupBy. -/
noncomputable def exampleGroupBy : GroupBy 2 2 := ⟨exampleOrderBy⟩

/-- The main bijectivity theorem applied to our concrete example. -/
theorem example_bijectivity : Function.Bijective exampleGroupBy.toEquiv :=
  lego_bijectivity 2 2 exampleGroupBy

/-! ### Example 6: FullLayout with group decomposition

Construct a FullLayout for the 6×4 matrix tiled into 2×2 blocks.
The FullLayout.toEquiv maps logical multi-indices through the
group decomposition and per-level permutations. -/

/-- A FullLayout for the 6×4 matrix with 2×2 tiling. -/
noncomputable def exampleFullLayout : FullLayout 2 2 where
  logicalShape := shape_6x4
  layout := exampleGroupBy
  hTiling := by
    intro i
    show ∏ k : Fin 2, exampleShapes k i = shape_6x4 i
    fin_cases i <;> native_decide

/-- The full layout bijection is bijective. -/
theorem example_full_layout_bijectivity : Function.Bijective exampleFullLayout.toEquiv :=
  lego_full_layout_bijectivity 2 2 exampleFullLayout

/-- The full layout permutation is bijective. -/
theorem example_full_layout_perm_bijectivity : Function.Bijective exampleFullLayout.toPermutation :=
  lego_full_layout_perm_bijectivity 2 2 exampleFullLayout

/-! ### Example 7: ExpandBy with bounds checking

Demonstrate that ExpandBy.apply correctly classifies in-bounds vs out-of-bounds. -/

/-- An ExpandBy for a 5×3 matrix extended to 6×4 with 2×2 tiling. -/
noncomputable def exampleExpandBy : ExpandBy 2 2 where
  origShape := ![5, 3]
  extShape := shape_6x4
  layout := exampleGroupBy
  hExtends := by intro i; fin_cases i <;> simp [shape_6x4]
  hTiling := by
    intro i
    show ∏ k : Fin 2, exampleShapes k i = shape_6x4 i
    fin_cases i <;> native_decide

/-- Index (1, 2) is in bounds for the 5×3 original shape. -/
example : InBounds (extShape := shape_6x4)
    (fun i => Fin.mk (![1, 2] i) (by fin_cases i <;> simp [shape_6x4])) ![5, 3] := by
  intro i; fin_cases i <;> simp

/-- Index (1, 3) is out of bounds for the 5×3 original shape (dim 1: 3 ≥ 3). -/
example : ¬ InBounds (extShape := shape_6x4)
    (fun i => Fin.mk (![1, 3] i) (by fin_cases i <;> simp [shape_6x4])) ![5, 3] := by
  intro h
  have := h ⟨1, by omega⟩
  simp at this

end LegoLean.Examples
