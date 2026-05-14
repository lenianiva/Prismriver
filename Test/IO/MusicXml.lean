import Prismriver.IO.MusicXml

namespace Prismriver.Test.IO.MusicXml

open Lean

def suite_xml : IO Unit := do
  let file ← IO.FS.readFile "./Test/IO/example.xml"
  let .ok elem := Xml.parse file | panic "failed"
  IO.println s!"{elem}"
