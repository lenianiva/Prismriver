import PrismriverTest.Common
import PrismriverTest.IO

namespace Prismriver.Test

def addPrefix (pref: String) (tests: List (String × α)): List (String  × α) :=
  tests.map (λ (name, x) => (pref ++ "/" ++ name, x))

abbrev TestTask := Task (Except IO.Error LSpec.TestSeq)
def filterTestGroup (tests : List (String × IO LSpec.TestSeq)) (nameFilter? : Option String)
  : IO (List (String × TestTask)) := do
  let tests : List (String × IO LSpec.TestSeq) := match nameFilter? with
    | .some nameFilter => tests.filter (λ (name, _) => nameFilter.isPrefixOf name)
    | .none => tests
  tests.mapM λ (name, t) => return (name, ← IO.asTask t)

/-- Runs test in parallel. Filters test name if given -/
def runTestTask (t : (String × TestTask)) : IO LSpec.TestSeq := do
  let (name, task) := t
  let v: Except IO.Error LSpec.TestSeq := task.get
  return match v with
  | .ok case => LSpec.group name case
  | .error e => expectationFailure name e.toString

end Prismriver.Test

open Prismriver.Test

/-- Main entry of tests; Provide an argument to filter tests by prefix -/
def main (args: List String) := do
  let nameFilter? := args.head?

  let suites: List (String × List (String × IO LSpec.TestSeq)) := [
    ("IO/MusicXml", IO.MusicXml.suite),
  ]
  let tests : List (String × IO LSpec.TestSeq) := suites.foldl (init := []) λ acc (name, suite) =>
    acc ++ (addPrefix name suite)
  LSpec.lspecEachIO (← filterTestGroup tests nameFilter?) runTestTask
