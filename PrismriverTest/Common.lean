import LSpec

namespace Prismriver.Test

def expectationFailure (desc: String) (error: String): LSpec.TestSeq := LSpec.test desc (LSpec.ExpectationFailure "ok _" error)
def assertUnreachable (message: String): LSpec.TestSeq := LSpec.check message false

abbrev TestT := StateRefT' IO.RealWorld LSpec.TestSeq

section Monadic

variable [Monad m] [MonadLiftT (ST IO.RealWorld) m]

def addTest (test: LSpec.TestSeq) : TestT m Unit := do
  set $ (← get) ++ test

def checkEq [DecidableEq α] [Repr α] (desc : String) (lhs rhs : α) : TestT m Unit := do
  addTest $ LSpec.check desc (lhs = rhs)
def checkTrue (desc : String) (flag : Bool) : TestT m Unit := do
  addTest $ LSpec.check desc flag
def checkFalse (desc : String) (flag : Bool) : TestT m Unit := do
  addTest $ LSpec.check desc !flag
def fail (desc : String) : TestT m Unit := do
  addTest $ LSpec.check desc false

def runTest (t: TestT m Unit): m LSpec.TestSeq :=
  Prod.snd <$> t.run LSpec.TestSeq.done
def runTestWithResult { α } (t: TestT m α): m (α × LSpec.TestSeq) :=
  t.run LSpec.TestSeq.done

end Monadic

end Prismriver.Test
