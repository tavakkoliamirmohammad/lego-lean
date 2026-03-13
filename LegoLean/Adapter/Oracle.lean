/-
Copyright (c) 2026 LEGO Layout Algebra Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Oracle Executable

`lake exe oracle` evaluates verified layouts at all coordinates and emits JSON.
Generated layout files register themselves via `initialize` blocks in OracleLib;
importing `LegoLean.Adapter.Generated` triggers those registrations.

## Usage
  lake exe oracle --list          # list registered layout names
  lake exe oracle <name>          # dump one layout as JSON
  lake exe oracle --all           # dump all layouts as JSON array
-/

import LegoLean.Adapter.OracleLib
import LegoLean.Adapter.Generated

open LegoLean.Oracle in
def main (args : List String) : IO Unit := do
  let entries ← oracleRegistry.get
  match args with
  | ["--list"] =>
    for e in entries do
      IO.println e.name
  | ["--all"] =>
    IO.print "["
    let mut first := true
    for e in entries do
      if !first then IO.print ","
      IO.println (entryToJSON e)
      first := false
    IO.println "]"
  | [name] =>
    match entries.find? (fun e => e.name == name) with
    | some entry =>
      IO.println (entryToJSON entry)
    | none =>
      IO.eprintln s!"Unknown layout: {name}"
      IO.eprintln "Available layouts:"
      for e in entries do
        IO.eprintln s!"  {e.name}"
      IO.Process.exit 1
  | _ =>
    IO.eprintln "Usage: oracle [--list | --all | <name>]"
    IO.Process.exit 1
