variable {F: Type}

-- g c' e''
-- lowercase letters are pitches
-- octave would be the # of octave suffixes. When octave < 0 it is a lower octave, when > 0 higher octave.
-- each ' suffix is a higher octave
-- each , suffix is a lower octave
structure Pitch (F : Type) where
  note: Char
  octave: Int

instance : Repr (Pitch F) where
  reprPrec p _ :=
    let modifier :=
      if p.octave > 0 then
        String.mk (List.replicate p.octave.natAbs '\'')
      else if p.octave < 0 then
        String.mk (List.replicate p.octave.natAbs ',')
      else
        ""
    p.note.toString ++ modifier

inductive Notation (F : Type) where
| pitch : Pitch F -> Notation F
