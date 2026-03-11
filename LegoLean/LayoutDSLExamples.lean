/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Layout DSL Examples

Exercises all DSL forms: identity, row, col, regP, genP, ExpandBy, 1D/2D/3D.
Each example compiles with zero `sorry` — bijectivity comes for free.

## References
- LEGO paper, Figure 2: 6×4 matrix example
- LEGO paper, Figure 6: 6×6 matrix example
-/

import LegoLean.LayoutDSL
import LegoLean.AntiDiagonal

namespace LegoLean.LayoutDSLExamples

/-! ### Example 1: 6×4 with identity permutations (explicit) -/

lego_full_layout dsl_row_6x4 : [6, 4] tileby [
  [3, 2] with regP id,
  [2, 2] with regP id
]

#check @dsl_row_6x4            -- FullLayout 2 2
#check @dsl_row_6x4_bijective  -- Function.Bijective dsl_row_6x4.toEquiv

-- Evaluate flat index for coordinate (1, 2)
#eval LegoLean.evalLayout dsl_row_6x4 [1, 2]

/-! ### Example 2: 6×4 with identity shorthand (omit perm spec) -/

lego_full_layout dsl_row_6x4_short : [6, 4] tileby [
  [3, 2],
  [2, 2]
]

#check @dsl_row_6x4_short

/-! ### Example 3: 6×4 with `row` sugar -/

lego_full_layout dsl_row_sugar : [6, 4] tileby [
  [3, 2] with row,
  [2, 2] with row
]

#check @dsl_row_sugar
#check @dsl_row_sugar_bijective

/-! ### Example 4: 6×4 with `col` sugar (column-major at tile level) -/

lego_full_layout dsl_col_sugar : [6, 4] tileby [
  [3, 2] with col,
  [2, 2] with row
]

#check @dsl_col_sugar
#check @dsl_col_sugar_bijective

/-! ### Example 5: 6×6 with antidiagonal GenP at block level -/

lego_full_layout dsl_6x6_antidiag : [6, 6] tileby [
  [3, 3] with genP (antiDiagGenP ![3, 3]),
  [2, 2] with regP id
]

#check @dsl_6x6_antidiag
#check @dsl_6x6_antidiag_bijective
#check @dsl_6x6_antidiag_perm_bijective

/-! ### Example 6: ExpandBy — 5×3 extended to 6×4 -/

lego_expand_layout dsl_expand_5x3 : [5, 3] → [6, 4] tileby [
  [3, 2],
  [2, 2]
]

#check @dsl_expand_5x3                  -- ExpandBy 2 2
#check @dsl_expand_5x3_layout_bijective -- Function.Bijective ...

-- Evaluate flat index for coordinate in original bounds (e.g. 1, 2)
#eval LegoLean.evalLayout dsl_expand_5x3 [1, 2]
-- Evaluate flat index for padded coordinate outside bounds (e.g. 5, 3) -> returns none
#eval LegoLean.evalLayout dsl_expand_5x3 [5, 3]

/-! ### Example 7: 1D layout -/

lego_full_layout dsl_1d : [12] tileby [
  [3],
  [4]
]

#check @dsl_1d

/-! ### Example 8: 3D layout -/

lego_full_layout dsl_3d : [8, 6, 4] tileby [
  [2, 3, 2],
  [4, 2, 2]
]

#check @dsl_3d
#check @dsl_3d_bijective

-- Evaluate flat index for 3D coordinate (1, 2, 3)
#eval LegoLean.evalLayout dsl_3d [1, 2, 3]

/-! ### Example 9: Single tile level -/

lego_full_layout dsl_single_tile : [6, 4] tileby [
  [6, 4]
]

#check @dsl_single_tile

/-! ### Example 10: Three tile levels -/

lego_full_layout dsl_three_levels : [24, 12] tileby [
  [2, 3],
  [3, 2],
  [4, 2]
]

#check @dsl_three_levels
#check @dsl_three_levels_bijective

/-! ### Example 11: 6×6 with dimension swap -/

lego_full_layout dsl_6x6_swap : [6, 6] tileby [
  [3, 3] with regP (Equiv.swap (0 : Fin 2) (1 : Fin 2)),
  [2, 2]
]

#check @dsl_6x6_swap

/-! ### Example 12: Mixed row/col -/

lego_full_layout dsl_mixed_row_col : [6, 6] tileby [
  [3, 3] with col,
  [2, 2] with row
]
#eval LegoLean.evalLayout dsl_mixed_row_col [0, 2]
#guard LegoLean.evalLayout dsl_mixed_row_col [0, 2] == some 12

#check @dsl_mixed_row_col
#check @dsl_mixed_row_col_bijective

/-! ### Example 13: ExpandBy with non-identity perm -/

lego_expand_layout dsl_expand_perm : [5, 5] → [6, 6] tileby [
  [3, 3] with genP (antiDiagGenP ![3, 3]),
  [2, 2]
]

#check @dsl_expand_perm
#check @dsl_expand_perm_layout_bijective

/-! ### Example 14: All col (column-major everywhere) -/

lego_full_layout dsl_all_col : [6, 4] tileby [
  [3, 2] with col,
  [2, 2] with col
]

#check @dsl_all_col
#check @dsl_all_col_bijective

/-! ### Example 15: row(4, 8) — row-major 4×8 -/

lego_full_layout dsl_row_4x8 : [4, 8] tileby [
  [2, 4] with row,
  [2, 2] with row
]

#check @dsl_row_4x8
#check @dsl_row_4x8_bijective
#check @dsl_row_4x8_perm_bijective

/-! ### Example 16: col(4, 8) — column-major 4×8 -/

lego_full_layout dsl_col_4x8 : [4, 8] tileby [
  [2, 4] with col,
  [2, 2] with col
]

#check @dsl_col_4x8
#check @dsl_col_4x8_bijective
#check @dsl_col_4x8_perm_bijective

/-! ### Example 17: row(4, 8) with single tile [4, 8] (no tiling, identity layout) -/

lego_full_layout dsl_row_4x8_full : [4, 8] tileby [
  [4, 8] with row
]

#check @dsl_row_4x8_full
#check @dsl_row_4x8_full_bijective
#check @dsl_row_4x8_full_perm_bijective

end LegoLean.LayoutDSLExamples
