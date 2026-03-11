/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Layout DSL — Compact Macros for LEGO Layouts

This file provides `lego_full_layout` and `lego_expand_layout` macros that
reduce the ~15-line boilerplate for constructing a FullLayout or ExpandBy
to ~4 lines. The generated code reuses all existing theorems from
`MainTheorem.lean`.

## Syntax

### FullLayout (tileby or groupby — same interface):
```
lego_full_layout foo : [6, 4] tileby [
  [3, 2] with row,
  [2, 2] with col
]

lego_full_layout bar : [6, 4] groupby [
  [3, 2] with col,
  [2, 2]
]
```

### Identity shorthand (omit perm spec):
```
lego_full_layout foo : [6, 4] tileby [
  [3, 2],
  [2, 2]
]
```

### ExpandBy (tileby or groupby):
```
lego_expand_layout baz : [5, 3] → [6, 4] tileby [
  [3, 2],
  [2, 2]
]
```

## Permutation specs
- `row` or `regP id` or `id` or omitted: identity (row-major)
- `col`: swap dims 0 and 1 (column-major, requires d ≥ 2)
- `regP <perm>`: arbitrary dimension permutation
- `genP <equiv>`: general user-defined bijection

## References
- LEGO paper, Section III-B: "Correctness"
-/

import LegoLean.MainTheorem
import Mathlib.Tactic.FinCases

namespace LegoLean

open Lean

/-! ## Syntax categories -/

declare_syntax_cat legoPermSpec
syntax "regP" "id" : legoPermSpec
syntax "regP" term : legoPermSpec
syntax "genP" term : legoPermSpec
syntax "id"        : legoPermSpec
syntax "row"       : legoPermSpec
syntax "col"       : legoPermSpec

declare_syntax_cat legoTileSpec
syntax "[" num,* "]" "with" legoPermSpec : legoTileSpec
syntax "[" num,* "]"                     : legoTileSpec

/-! ## Main syntax -/

syntax (name := legoFullLayoutGB)
  "lego_full_layout" ident " : " "[" num,* "]" " groupby " "[" legoTileSpec,* "]" : command

syntax (name := legoExpandLayoutGB)
  "lego_expand_layout" ident " : " "[" num,* "]" " → " "[" num,* "]"
    " groupby " "[" legoTileSpec,* "]" : command

syntax (name := legoFullLayout)
  "lego_full_layout" ident " : " "[" num,* "]" " tileby " "[" legoTileSpec,* "]" : command

syntax (name := legoExpandLayout)
  "lego_expand_layout" ident " : " "[" num,* "]" " → " "[" num,* "]"
    " tileby " "[" legoTileSpec,* "]" : command

/-! ## Helpers -/

private def permSpecToTerm (spec : TSyntax `legoPermSpec) (d : Nat) :
    MacroM (TSyntax `term) := do
  let dLit := Syntax.mkNumLit (toString d)
  match spec with
  | `(legoPermSpec| regP id) => `(TilePerm.regP (Equiv.refl (Fin $dLit)))
  | `(legoPermSpec| regP $t:term) => `(TilePerm.regP $t)
  | `(legoPermSpec| genP $t:term) => `(TilePerm.genP $t)
  | `(legoPermSpec| id) => `(TilePerm.regP (Equiv.refl (Fin $dLit)))
  -- `row` = identity, `col` = full dimension reversal (i ↦ d-1-i)
  | `(legoPermSpec| row) => `(TilePerm.regP (Equiv.refl (Fin $dLit)))
  | `(legoPermSpec| col) => do
    if d < 2 then Macro.throwError "col requires at least 2 dimensions"
    `(TilePerm.regP (dimRevEquiv $dLit))
  | _ => Macro.throwUnsupported

private def mkVecLit (nums : Array (TSyntax `num)) : MacroM (TSyntax `term) := do
  match nums.toList with
  | [a] => `(![$a])
  | [a, b] => `(![$a, $b])
  | [a, b, c] => `(![$a, $b, $c])
  | [a, b, c, dd] => `(![$a, $b, $c, $dd])
  | [a, b, c, dd, e] => `(![$a, $b, $c, $dd, $e])
  | [a, b, c, dd, e, f] => `(![$a, $b, $c, $dd, $e, $f])
  | _ => Macro.throwError "shapes with 0 or more than 6 dimensions are not supported"

private def mkTermVecLit (terms : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  match terms.toList with
  | [a] => `(![$a])
  | [a, b] => `(![$a, $b])
  | [a, b, c] => `(![$a, $b, $c])
  | [a, b, c, dd] => `(![$a, $b, $c, $dd])
  | [a, b, c, dd, e] => `(![$a, $b, $c, $dd, $e])
  | _ => Macro.throwError "more than 5 tiling levels are not supported"

private def parseTileSpec (tile : TSyntax `legoTileSpec) :
    MacroM (Array (TSyntax `num) × Option (TSyntax `legoPermSpec)) := do
  match tile with
  | `(legoTileSpec| [ $dims,* ] with $p:legoPermSpec) =>
    return (dims.getElems, some p)
  | `(legoTileSpec| [ $dims,* ]) =>
    return (dims.getElems, none)
  | _ => Macro.throwUnsupported

private def mkPermsBody (permTerms : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  match permTerms.toList with
  | [p0] =>
    `(fun _ => $p0)
  | [p0, p1] =>
    `(fun k => match k with | ⟨0, _⟩ => $p0 | ⟨1, _⟩ => $p1)
  | [p0, p1, p2] =>
    `(fun k => match k with | ⟨0, _⟩ => $p0 | ⟨1, _⟩ => $p1 | ⟨2, _⟩ => $p2)
  | [p0, p1, p2, p3] =>
    `(fun k => match k with
      | ⟨0, _⟩ => $p0 | ⟨1, _⟩ => $p1 | ⟨2, _⟩ => $p2 | ⟨3, _⟩ => $p3)
  | [p0, p1, p2, p3, p4] =>
    `(fun k => match k with
      | ⟨0, _⟩ => $p0 | ⟨1, _⟩ => $p1 | ⟨2, _⟩ => $p2 | ⟨3, _⟩ => $p3
      | ⟨4, _⟩ => $p4)
  | _ => Macro.throwError "at least 1 and at most 5 tiling levels supported"

private def defaultPermTerm (d : Nat) : MacroM (TSyntax `term) := do
  `(TilePerm.regP (Equiv.refl (Fin $(Syntax.mkNumLit (toString d)))))

private def parseTiles (tilesArr : TSyntaxArray `legoTileSpec) (d : Nat) :
    MacroM (Array (TSyntax `term) × Array (TSyntax `term)) := do
  let mut tileShapeTerms : Array (TSyntax `term) := #[]
  let mut permTerms : Array (TSyntax `term) := #[]
  for tile in tilesArr do
    let (dims, permOpt) ← parseTileSpec tile
    if dims.size != d then
      Macro.throwError s!"tile dimension mismatch: expected {d}, got {dims.size}"
    tileShapeTerms := tileShapeTerms.push (← mkVecLit dims)
    permTerms := permTerms.push (← match permOpt with
      | some spec => permSpecToTerm spec d
      | none => defaultPermTerm d)
  -- Reverse: DSL convention is outermost-first, but finPiFinEquiv uses
  -- index 0 as least significant (innermost). Reversing aligns the two.
  return (tileShapeTerms.reverse, permTerms.reverse)

/-! ## Macro rules: tileby → TileBy -/

macro_rules
  | `(command| lego_full_layout $name:ident : [ $shapeDims,* ] tileby [ $tiles,* ]) => do
    let shapeDimsArr := shapeDims.getElems
    let tilesArr := tiles.getElems
    let d := shapeDimsArr.size
    let q := tilesArr.size
    let dLit := Syntax.mkNumLit (toString d)
    let qLit := Syntax.mkNumLit (toString q)
    let logicalShapeTerm ← mkVecLit shapeDimsArr
    let (tileShapeTerms, permTerms) ← parseTiles tilesArr d
    let shapesVecTerm ← mkTermVecLit tileShapeTerms
    let permsBody ← mkPermsBody permTerms

    let nameStr := name.getId.toString
    let shapesId := mkIdent (Name.mkSimple (nameStr ++ "__shapes"))
    let tileById := mkIdent (Name.mkSimple (nameStr ++ "__tileBy"))
    let bijId := mkIdent (Name.mkSimple (nameStr ++ "_bijective"))
    let permBijId := mkIdent (Name.mkSimple (nameStr ++ "_perm_bijective"))

    let cmd1 ← `(command|
      private def $shapesId : Fin $qLit → Shape $dLit := $shapesVecTerm)
    let cmd2 ← `(command|
      def $tileById : TileBy $dLit $qLit :=
        ⟨$shapesId, $permsBody⟩)
    let cmd3 ← `(command|
      def $name : FullLayout $dLit $qLit :=
        TileBy.toFullLayout $tileById $logicalShapeTerm
          (by intro i
              show ∏ k : Fin $qLit, $shapesId k i = $logicalShapeTerm i
              fin_cases i <;> native_decide))
    let cmd4 ← `(command|
      theorem $bijId : Function.Bijective (FullLayout.toEquiv $name) :=
        FullLayout.bijective $name)
    let cmd5 ← `(command|
      theorem $permBijId : Function.Bijective (FullLayout.toPermutation $name) :=
        Equiv.bijective (FullLayout.toPermutation $name))
    return mkNullNode #[cmd1, cmd2, cmd3, cmd4, cmd5]

macro_rules
  | `(command| lego_expand_layout $name:ident : [ $origDims,* ] → [ $extDims,* ]
      tileby [ $tiles,* ]) => do
    let origDimsArr := origDims.getElems
    let extDimsArr := extDims.getElems
    let tilesArr := tiles.getElems
    let d := extDimsArr.size
    let q := tilesArr.size
    if origDimsArr.size != d then
      Macro.throwError
        s!"original shape dimension mismatch: expected {d}, got {origDimsArr.size}"
    let dLit := Syntax.mkNumLit (toString d)
    let qLit := Syntax.mkNumLit (toString q)
    let origShapeTerm ← mkVecLit origDimsArr
    let extShapeTerm ← mkVecLit extDimsArr
    let (tileShapeTerms, permTerms) ← parseTiles tilesArr d
    let shapesVecTerm ← mkTermVecLit tileShapeTerms
    let permsBody ← mkPermsBody permTerms

    let nameStr := name.getId.toString
    let shapesId := mkIdent (Name.mkSimple (nameStr ++ "__shapes"))
    let tileById := mkIdent (Name.mkSimple (nameStr ++ "__tileBy"))
    let bijId := mkIdent (Name.mkSimple (nameStr ++ "_layout_bijective"))

    let cmd1 ← `(command|
      private def $shapesId : Fin $qLit → Shape $dLit := $shapesVecTerm)
    let cmd2 ← `(command|
      def $tileById : TileBy $dLit $qLit :=
        ⟨$shapesId, $permsBody⟩)
    let cmd3 ← `(command|
      def $name : ExpandBy $dLit $qLit :=
        ⟨$origShapeTerm, $extShapeTerm, TileBy.toGroupBy $tileById,
         by intro i; fin_cases i <;> simp,
         by intro i
            show ∏ k : Fin $qLit, $shapesId k i = $extShapeTerm i
            fin_cases i <;> native_decide⟩)
    let cmd4 ← `(command|
      theorem $bijId : Function.Bijective (GroupBy.toEquiv (ExpandBy.layout $name)) :=
        ExpandBy.layout_bijective $name)
    return mkNullNode #[cmd1, cmd2, cmd3, cmd4]

/-! ## Macro rules: groupby → GroupBy directly -/

macro_rules
  | `(command| lego_full_layout $name:ident : [ $shapeDims,* ] groupby [ $tiles,* ]) => do
    let shapeDimsArr := shapeDims.getElems
    let tilesArr := tiles.getElems
    let d := shapeDimsArr.size
    let q := tilesArr.size
    let dLit := Syntax.mkNumLit (toString d)
    let qLit := Syntax.mkNumLit (toString q)
    let logicalShapeTerm ← mkVecLit shapeDimsArr
    let (tileShapeTerms, permTerms) ← parseTiles tilesArr d
    let shapesVecTerm ← mkTermVecLit tileShapeTerms
    let permsBody ← mkPermsBody permTerms

    let nameStr := name.getId.toString
    let shapesId := mkIdent (Name.mkSimple (nameStr ++ "__shapes"))
    let groupById := mkIdent (Name.mkSimple (nameStr ++ "__groupBy"))
    let bijId := mkIdent (Name.mkSimple (nameStr ++ "_bijective"))
    let permBijId := mkIdent (Name.mkSimple (nameStr ++ "_perm_bijective"))

    let cmd1 ← `(command|
      private def $shapesId : Fin $qLit → Shape $dLit := $shapesVecTerm)
    let cmd2 ← `(command|
      def $groupById : GroupBy $dLit $qLit :=
        GroupBy.ofOrderBy ⟨$shapesId, $permsBody⟩)
    let cmd3 ← `(command|
      def $name : FullLayout $dLit $qLit :=
        ⟨$logicalShapeTerm, $groupById,
          by intro i
             show ∏ k : Fin $qLit, $shapesId k i = $logicalShapeTerm i
             fin_cases i <;> native_decide⟩)
    let cmd4 ← `(command|
      theorem $bijId : Function.Bijective (FullLayout.toEquiv $name) :=
        FullLayout.bijective $name)
    let cmd5 ← `(command|
      theorem $permBijId : Function.Bijective (FullLayout.toPermutation $name) :=
        Equiv.bijective (FullLayout.toPermutation $name))
    return mkNullNode #[cmd1, cmd2, cmd3, cmd4, cmd5]

macro_rules
  | `(command| lego_expand_layout $name:ident : [ $origDims,* ] → [ $extDims,* ]
      groupby [ $tiles,* ]) => do
    let origDimsArr := origDims.getElems
    let extDimsArr := extDims.getElems
    let tilesArr := tiles.getElems
    let d := extDimsArr.size
    let q := tilesArr.size
    if origDimsArr.size != d then
      Macro.throwError
        s!"original shape dimension mismatch: expected {d}, got {origDimsArr.size}"
    let dLit := Syntax.mkNumLit (toString d)
    let qLit := Syntax.mkNumLit (toString q)
    let origShapeTerm ← mkVecLit origDimsArr
    let extShapeTerm ← mkVecLit extDimsArr
    let (tileShapeTerms, permTerms) ← parseTiles tilesArr d
    let shapesVecTerm ← mkTermVecLit tileShapeTerms
    let permsBody ← mkPermsBody permTerms

    let nameStr := name.getId.toString
    let shapesId := mkIdent (Name.mkSimple (nameStr ++ "__shapes"))
    let groupById := mkIdent (Name.mkSimple (nameStr ++ "__groupBy"))
    let bijId := mkIdent (Name.mkSimple (nameStr ++ "_layout_bijective"))

    let cmd1 ← `(command|
      private def $shapesId : Fin $qLit → Shape $dLit := $shapesVecTerm)
    let cmd2 ← `(command|
      def $groupById : GroupBy $dLit $qLit :=
        GroupBy.ofOrderBy ⟨$shapesId, $permsBody⟩)
    let cmd3 ← `(command|
      def $name : ExpandBy $dLit $qLit :=
        ⟨$origShapeTerm, $extShapeTerm, $groupById,
         by intro i; fin_cases i <;> simp,
         by intro i
            show ∏ k : Fin $qLit, $shapesId k i = $extShapeTerm i
            fin_cases i <;> native_decide⟩)
    let cmd4 ← `(command|
      theorem $bijId : Function.Bijective (GroupBy.toEquiv (ExpandBy.layout $name)) :=
        ExpandBy.layout_bijective $name)
    return mkNullNode #[cmd1, cmd2, cmd3, cmd4]

/-! ## Layout Evaluation -/

/-- A typeclass for evaluating layouts with a list of coordinates. -/
class EvalLayout (L : Type) (d : outParam ℕ) where
  eval : L → (Fin d → ℕ) → Option ℕ

instance {d q} : EvalLayout (FullLayout d q) d where
  eval l coords :=
    if h : ∀ i, coords i < l.logicalShape i then
      let multiIdx : MultiIndex l.logicalShape := fun i => ⟨coords i, h i⟩
      some (l.toEquiv multiIdx).val
    else
      none

instance {d q} : EvalLayout (ExpandBy d q) d where
  eval l coords :=
    if h : ∀ i, coords i < l.extShape i then
      let multiIdx : MultiIndex l.extShape := fun i => ⟨coords i, h i⟩
      match l.apply multiIdx with
      | some finIdx => some finIdx.val
      | none => none
    else
      none

/-- Evaluates a layout (FullLayout or ExpandBy) on a list of nat coordinates.
    Usage: `#eval evalLayout my_layout [1, 2, ...]` -/
def evalLayout {L d} [EvalLayout L d] (l : L) (lst : List ℕ) : Option ℕ :=
  if lst.length = d then
    let coords := fun (i : Fin d) =>
      if h_bounds : i.val < lst.length then
        lst.get ⟨i.val, h_bounds⟩
      else
        0
    EvalLayout.eval l coords
  else
    none

end LegoLean
