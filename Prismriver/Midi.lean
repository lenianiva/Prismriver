import Lean.Elab

open Lean

namespace Prismriver

def play (aldaCode : String) : IO UInt32 := do
  let lockFile := "/tmp/prismriver-alda.lock"
  let hLock ← IO.FS.Handle.mk lockFile .write
  let flag ← hLock.tryLock
  if !flag then
    return 0
  let ch ← IO.Process.spawn { cmd := "alda", args := #["play", "--code", aldaCode] }
  let ret ← ch.wait
  hLock.unlock
  return ret

elab "#play" t:term : command => do
  let notes ← Elab.Command.liftTermElabM do
    let type ← Elab.Term.elabType (← `(term|List String))
    let li ← Elab.Term.elabTerm t .none
    let notes ← unsafe do
      Meta.evalExpr (List String) type li
    return notes
  let notes := " ".intercalate notes
  let code := s!"piano: {notes}"

  logInfo s!"piano: {code}"
  let ret ← play code
  if ret ≠ 0 then
    logError s!"Subprocess failed: {ret}"
