import Prismriver

open Prismriver.Classical

-- Examples
#eval (⟨.c, .natural⟩: Tone)
#eval (⟨.d, .sharp⟩: Tone)
#eval ({ name :=.d, octave := 4 }: Pitch)
#eval (diatonic ⟨.e, .sharp⟩ .d).name
#eval (diatonic ⟨.d, .natural⟩ .a).pitches 5
#eval (diatonic ⟨.f, .natural⟩ .d).pitches 5
