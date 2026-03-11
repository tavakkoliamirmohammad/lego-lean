/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Layout DSL — Compact Macros for LEGO Layouts

This file provides `lego_full_layout` and `lego_expand_layout` macros that
reduce the ~15-line boilerplate for constructing a FullLayout or ExpandBy
to ~4 lines. The generated code reuses all existing theorems from
`MainTheorem.lean`.

## Syntax

### FullLayout:
```
lego_full_layout foo : [6, 4] tileby [
  [3, 2] with row,
  [2, 2] with col
]
```

### Identity shorthand (omit perm spec):
```
lego_full_layout foo : [6, 4] tileby [
  [3, 2],
  [2, 2]
]
```

### ExpandBy:
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
  | `(legoPermSpec| row) => `(TilePerm.regP (Equiv.refl (Fin $dLit)))
  | `(legoPermSpec| col) => do
    if d < 2 then Macro.throwError "col requires at least 2 dimensions"
    `(TilePerm.regP (Equiv.swap (0 : Fin $dLit) (1 : Fin $dLit)))
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
  return (tileShapeTerms, permTerms)

/-! ## Macro rules -/

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
    let orderById := mkIdent (Name.mkSimple (nameStr ++ "__orderBy"))
    let groupById := mkIdent (Name.mkSimple (nameStr ++ "__groupBy"))
    let bijId := mkIdent (Name.mkSimple (nameStr ++ "_bijective"))
    let permBijId := mkIdent (Name.mkSimple (nameStr ++ "_perm_bijective"))

    let cmd1 ← `(command|
      private def $shapesId : Fin $qLit → Shape $dLit := $shapesVecTerm)
    let cmd2 ← `(command|
      noncomputable def $orderById : OrderBy $dLit $qLit :=
        ⟨$shapesId, $permsBody⟩)
    let cmd3 ← `(command|
      noncomputable def $groupById : GroupBy $dLit $qLit :=
        GroupBy.ofOrderBy $orderById)
    let cmd4 ← `(command|
      noncomputable def $name : FullLayout $dLit $qLit :=
        ⟨$logicalShapeTerm, $groupById,
         by intro i
            show ∏ k : Fin $qLit, $shapesId k i = $logicalShapeTerm i
            fin_cases i <;> native_decide⟩)
    let cmd5 ← `(command|
      theorem $bijId : Function.Bijective (FullLayout.toEquiv $name) :=
        FullLayout.bijective $name)
    let cmd6 ← `(command|
      theorem $permBijId : Function.Bijective (FullLayout.toPermutation $name) :=
        Equiv.bijective (FullLayout.toPermutation $name))
    return mkNullNode #[cmd1, cmd2, cmd3, cmd4, cmd5, cmd6]

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
    let orderById := mkIdent (Name.mkSimple (nameStr ++ "__orderBy"))
    let groupById := mkIdent (Name.mkSimple (nameStr ++ "__groupBy"))
    let bijId := mkIdent (Name.mkSimple (nameStr ++ "_layout_bijective"))

    let cmd1 ← `(command|
      private def $shapesId : Fin $qLit → Shape $dLit := $shapesVecTerm)
    let cmd2 ← `(command|
      noncomputable def $orderById : OrderBy $dLit $qLit :=
        ⟨$shapesId, $permsBody⟩)
    let cmd3 ← `(command|
      noncomputable def $groupById : GroupBy $dLit $qLit :=
        GroupBy.ofOrderBy $orderById)
    let cmd4 ← `(command|
      noncomputable def $name : ExpandBy $dLit $qLit :=
        ⟨$origShapeTerm, $extShapeTerm, $groupById,
         by intro i; fin_cases i <;> simp,
         by intro i
            show ∏ k : Fin $qLit, $shapesId k i = $extShapeTerm i
            fin_cases i <;> native_decide⟩)
    let cmd5 ← `(command|
      theorem $bijId : Function.Bijective (GroupBy.toEquiv (ExpandBy.layout $name)) :=
        ExpandBy.layout_bijective $name)
    return mkNullNode #[cmd1, cmd2, cmd3, cmd4, cmd5]

end LegoLean
