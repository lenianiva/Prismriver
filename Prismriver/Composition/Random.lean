import Prismriver.Repr.Classical

namespace Prismriver

open Classical

/-- Compositional governance and harmonicity control -/
structure Governance where
  consonant : List Interval := [Interval.ma2, Interval.ma3, Interval.p4, Interval.p5]
  h_nonempty : consonant ≠ []

namespace Governance

protected def default : Governance := {
    h_nonempty := by simp,
  }

end Governance

/-- Compose a random piece by walking on intervals -/
def randomWalk { Gen : Type } [RandomGen Gen] (g : Gen) (n : Nat) (last : Pitch)
  : ReaderM Governance (List Pitch) := do
  let permitted := (← read).consonant
  let (li, _) ← n.foldM (α := (List Pitch) × Gen) (init := ([last], g))
    λ _i _h (li, g) => do
      let (i_interval, g) := randNat g 0 (permitted.length - 1)
      let interval := permitted[i_interval]!
      let pitch := interval • li.head!
      pure (pitch :: li, g)
  return li


#eval randomWalk (mkStdGen) 5 Pitch.c4 |>.run .default
