namespace Prismriver

class Time (I D : Type) extends Add D, HAdd I D I, Neg D, SMul Int D where
  zero : D
  /- Maximum time within a bar -/
  bar : D := zero

instance : Time Int Int where
  zero := 0

instance : Time Rat Rat where
  zero := 0

structure MeasuredTime where
  bar : Int
  offset : Rat

instance : ToString MeasuredTime where
  toString i := s!"{i.bar}.{i.offset}"

instance timeSignature (top bot : Nat)
  : Time MeasuredTime Rat where
  zero := 0
  bar := mkRat top bot
  hAdd t d := { t with offset := t.offset + d }
