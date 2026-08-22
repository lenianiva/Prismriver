import Prismriver.Repr.Classical
import Prismriver.Repr.Score
import Lean.Elab

namespace Prismriver

def play (aldaCode : String) : IO UInt32 := do
  let lockFile := "/tmp/prismriver-alda.lock"
  let hLock ← IO.FS.Handle.mk lockFile .write
  let flag ← hLock.tryLock
  if !flag then
    return 0
  let ret ← IO.Process.output { cmd := "alda", args := #["play", "--wait"] } aldaCode
  hLock.unlock
  return ret.exitCode

open Lean in
elab "#play" e:term : command => do
  let notes ← Elab.Command.liftTermElabM do
    let type ← Elab.Term.elabType (← `(term|List Prismriver.Classical.Note))
    let li ← Elab.Term.elabTerm e (.some type)
    let notes ← unsafe do
      Meta.evalExpr (List Classical.Note) type li
    return notes

  let notes := " ".intercalate $ notes.map λ note =>
    s!"o{note.pitch.octave + 4} {note.pitch.hep}"
  let code := s!"piano: {notes}"

  logInfo s!"{code}"
  let ret ← play code
  if ret ≠ 0 then
    throwError s!"Subprocess failed: {ret}"
