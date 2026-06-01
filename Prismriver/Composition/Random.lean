import Prismriver.Repr.Classical

namespace Prismriver.Composition

/-- Generate weighted random variable -/
def randWeighted { gen } [RandomGen gen] (g : gen) (weights : Array Nat) : Nat × gen := Id.run do
  -- "Loaded Die from Biased Coins"
  let mut mass := weights.sum
  let mut g := g
  for (p, i) in weights.zipIdx do
    let (z, g') := randNat g 0 mass
    g := g'
    if z < p then
      return (i, g)
    mass := mass - p
  return (0, g)

/-- A monad with access to a random entropy source -/
class MonadRandom ( g : outParam Type ) [RandomGen g] (m : Type → Type) [Monad m] where
  getGen : m g
  setGen : g → m Unit
  generate { α } (f : g → (α × g)) : m α := do
    let (a, g) := f (← getGen)
    setGen g
    return a
  genRange (lo hi : Nat) : m Nat := generate (randNat · lo hi)
  genWeighted (weights : Array Nat) : m Nat := generate (randWeighted · weights)

@[always_inline]
instance (g m n) [Monad m] [Monad n] [MonadLift m n] [RandomGen g] [MonadRandom g m] : MonadRandom g n where
  getGen := liftM (MonadRandom.getGen : m g)
  setGen := fun g => liftM (MonadRandom.setGen g : m Unit)

def genRange { g } [RandomGen g] { m } [Monad m] [MonadRandom g m] := @MonadRandom.genRange g _ m _ _
def genWeighted { g } [RandomGen g] { m } [Monad m] [MonadRandom g m] := @MonadRandom.genWeighted g _ m _ _
-- FIXME: Do not use `Inhabited`. Use nonempty proof instead
def genChoice { g α } [Inhabited α] [RandomGen g] { m } [Monad m] [MonadRandom g m] (weights : Array Nat) (objects : Array α) : m α := do
  let i ← genWeighted weights
  return objects[i]!

abbrev MonadStdGen := MonadRandom StdGen
abbrev RandomT := StateT StdGen

instance { m } [ Monad m ] : MonadStdGen (RandomT m) where
  getGen := get
  setGen := set

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
