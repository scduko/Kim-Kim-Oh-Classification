/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Authors of the upstream replay procedure: Kim Morrison, Sebastian Ullrich
-/
import Lean.CoreM
import Lean.Replay

/-! Replay the declarations of one compiled module in the environment of its imports.
The replay procedure is adapted from `replayFromImports` in Lean 4.36.0's
`src/LeanChecker.lean`. The workflow supplies one full module name. -/

open Lean

unsafe def main (args : List String) : IO Unit := do
  let [arg] := args | throw <| IO.userError "expected one exact module name"
  let moduleName := arg.toName
  if moduleName.isAnonymous then throw <| IO.userError "empty module name"
  initSearchPath (← findSysroot)
  let olean ← findOLean moduleName
  unless (← olean.pathExists) do
    throw <| IO.userError s!"missing object file for {moduleName}: {olean}"
  let mut files := #[olean]
  let server := OLeanLevel.server.adjustFileName olean
  if (← server.pathExists) then
    files := files.push server
    let priv := OLeanLevel.private.adjustFileName olean
    if (← priv.pathExists) then files := files.push priv
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then throw <| IO.userError s!"empty module data for {moduleName}" else
  let imports := parts[0].1.imports
  let (_, state) ← importModulesCore imports |>.run
  let env ← finalizeImport state imports {} 0 false false (isModule := true)
  -- The last (most private) part also contains the constants of the preceding parts.
  let data := parts[parts.size - 1].1
  let mut constants := {}
  for name in data.constNames, ci in data.constants do
    constants := constants.insert name ci
  discard <| env.toKernelEnv.replay constants
  env.freeRegions
