namespace Prismriver

class Time (I D : Type) extends Add D, HAdd I D I, HSub I I D, SMul Int D, ToString I where
  zero : D
  bar : D := zero

instance : Time Int Int where
  zero := 0

instance : Time Rat Rat where
  zero := 0

instance timeSignature (top bot : Nat)
  : Time Rat Rat where
  zero := 0
  bar := mkRat top bot
  toString i :=
    let bar := mkRat top bot
    let barN := (i / bar).floor
    let offset := i - barN * bar
    if barN == 0 then
      s!"{offset}"
    else
      s!"{barN}.{offset}"
