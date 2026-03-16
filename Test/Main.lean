import Test.IO

open Prismriver

def main : IO UInt32 := do
  Test.IO.MusicXml.suite_xml
  return 0
