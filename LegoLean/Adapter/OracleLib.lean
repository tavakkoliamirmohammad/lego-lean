/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Oracle Library

Provides the oracle registry and JSON output helpers for verified layout evaluation.
Generated layout files register themselves via `initialize` blocks; the oracle
executable (`lake exe oracle`) reads the registry and dumps lookup tables as JSON.
-/

import LegoLean.LayoutDSL

namespace LegoLean.Oracle

/-- An oracle entry: a named layout with its shape and evaluation function. -/
structure OracleEntry where
  name : String
  shape : List ℕ
  evalFn : List ℕ → Option ℕ

/-- Global mutable registry of oracle entries, populated by `initialize` blocks
    in generated layout files. -/
initialize oracleRegistry : IO.Ref (Array OracleEntry) ← IO.mkRef #[]

/-- Register a layout for oracle evaluation. Called from `initialize` blocks
    in generated files. -/
def register (entry : OracleEntry) : IO Unit :=
  oracleRegistry.modify (·.push entry)

/-- Enumerate all coordinate tuples for a given shape in row-major order.
    Example: `allCoords [2, 3]` = `[[0,0],[0,1],[0,2],[1,0],[1,1],[1,2]]` -/
def allCoords : List ℕ → List (List ℕ)
  | [] => [[]]
  | d :: rest =>
    let subCoords := allCoords rest
    ((List.range d).map fun i =>
      subCoords.map fun sub => i :: sub).flatten

/-- Format coordinates as a JSON array key: `[0,1,2]` -/
def coordToKey (coords : List ℕ) : String :=
  "[" ++ String.intercalate "," (coords.map toString) ++ "]"

/-- Serialize an oracle entry as a JSON object string. -/
def entryToJSON (entry : OracleEntry) : String :=
  let coords := allCoords entry.shape
  let pairs : List String := coords.map fun c =>
    let key := coordToKey c
    let val := match entry.evalFn c with
      | some v => toString v
      | none => "null"
    "\"" ++ key ++ "\": " ++ val
  let shapeStr := "[" ++ String.intercalate ", " (entry.shape.map toString) ++ "]"
  let tableStr := String.intercalate ", " pairs
  "{\"name\": \"" ++ entry.name ++ "\", \"shape\": " ++ shapeStr ++
    ", \"table\": {" ++ tableStr ++ "}}"

end LegoLean.Oracle
