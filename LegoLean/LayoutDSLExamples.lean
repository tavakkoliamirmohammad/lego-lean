/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Layout DSL Examples

Progressively complex examples exercising all DSL forms:
tileby, groupby, row, col, regP, genP, ExpandBy, 1D/2D/3D, multi-level.
Each example compiles with zero `sorry` — bijectivity comes for free.

## References
- LEGO paper, Figure 2: 6×4 matrix example
- LEGO paper, Figure 6: 6×6 matrix example
-/

import LegoLean.LayoutDSL
import LegoLean.AntiDiagonal

namespace LegoLean.LayoutDSLExamples

/-! ## 1D -/

/-! ### 1D row-major, single tile (identity layout) -/

lego_full_layout ex_1d_single : [12] tileby [
  [12]
]

#check @ex_1d_single  -- FullLayout 1 1

/-! ### 1D row-major, two tile levels -/

lego_full_layout ex_1d_tiled : [12] tileby [
  [3],
  [4]
]

#check @ex_1d_tiled
#check @ex_1d_tiled_bijective

/-! ## 2D — tileby (→ TileBy) -/

/-! ### 2D single tile (no tiling, just flattening) -/

lego_full_layout ex_2d_single : [4, 8] tileby [
  [4, 8]
]

#check @ex_2d_single
#check @ex_2d_single_bijective

/-! ### 2D row-major, identity shorthand (omit perm spec) -/

lego_full_layout ex_2d_row : [6, 4] tileby [
  [3, 2],
  [2, 2]
]

#check @ex_2d_row
#check @ex_2d_row_bijective
#eval evalLayout ex_2d_row [1, 2]

/-! ### 2D row-major, explicit `row` sugar -/

lego_full_layout ex_2d_row_explicit : [4, 8] tileby [
  [2, 4] with row,
  [2, 2] with row
]

#check @ex_2d_row_explicit
#check @ex_2d_row_explicit_bijective

/-! ### 2D col-major at outer tile level -/

lego_full_layout ex_2d_col : [6, 4] tileby [
  [3, 2] with col,
  [2, 2]
]

#check @ex_2d_col
#check @ex_2d_col_bijective

/-! ### 2D col-major everywhere -/

lego_full_layout ex_2d_all_col : [4, 8] tileby [
  [2, 4] with col,
  [2, 2] with col
]

#check @ex_2d_all_col
#check @ex_2d_all_col_bijective

/-! ### 2D mixed row/col -/

lego_full_layout ex_2d_mixed : [6, 6] tileby [
  [3, 3] with col,
  [2, 2] with row
]

#eval evalLayout ex_2d_mixed [0, 2]
#guard evalLayout ex_2d_mixed [0, 2] == some 12
#check @ex_2d_mixed_bijective

/-! ### 2D three tile levels -/

lego_full_layout ex_2d_three_levels : [24, 12] tileby [
  [2, 3],
  [3, 2],
  [4, 2]
]

#check @ex_2d_three_levels
#check @ex_2d_three_levels_bijective

/-! ### 2D explicit regP (dimension swap) -/

lego_full_layout ex_2d_regp : [6, 6] tileby [
  [3, 3] with regP (Equiv.swap (0 : Fin 2) (1 : Fin 2)),
  [2, 2]
]

#check @ex_2d_regp

/-! ### 2D genP (antidiagonal bijection) -/

lego_full_layout ex_2d_genp : [6, 6] tileby [
  [3, 3] with genP (antiDiagGenP ![3, 3]),
  [2, 2]
]

#check @ex_2d_genp
#check @ex_2d_genp_bijective
#check @ex_2d_genp_perm_bijective

/-! ## 3D -/

lego_full_layout ex_3d : [8, 6, 4] tileby [
  [2, 3, 2],
  [4, 2, 2]
]

#check @ex_3d
#check @ex_3d_bijective
#eval evalLayout ex_3d [1, 2, 3]

/-! ### 3D with col (full dimension reversal) -/

lego_full_layout ex_3d_col : [8, 6, 4] tileby [
  [2, 3, 2] with col,
  [4, 2, 2]
]

#check @ex_3d_col
#check @ex_3d_col_bijective

/-! ## 2D — groupby (→ GroupBy directly) -/

lego_full_layout ex_2d_groupby : [6, 4] groupby [
  [3, 2] with col,
  [2, 2]
]

#check @ex_2d_groupby
#check @ex_2d_groupby_bijective

/-! ## ExpandBy -/

/-! ### ExpandBy with tileby -/

lego_expand_layout ex_expand : [5, 3] → [6, 4] tileby [
  [3, 2],
  [2, 2]
]

#check @ex_expand                  -- ExpandBy 2 2
#check @ex_expand_layout_bijective
#eval evalLayout ex_expand [1, 2]  -- in-bounds → some
#eval evalLayout ex_expand [5, 3]  -- out-of-bounds → none

/-! ### ExpandBy with groupby -/

lego_expand_layout ex_expand_groupby : [5, 3] → [6, 4] groupby [
  [3, 2],
  [2, 2]
]

#check @ex_expand_groupby
#check @ex_expand_groupby_layout_bijective

/-! ### ExpandBy with genP (antidiagonal) -/

lego_expand_layout ex_expand_genp : [5, 5] → [6, 6] tileby [
  [3, 3] with genP (antiDiagGenP ![3, 3]),
  [2, 2]
]

#check @ex_expand_genp
#check @ex_expand_genp_layout_bijective

end LegoLean.LayoutDSLExamples
