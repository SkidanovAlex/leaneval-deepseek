import Submission.Work.PTCert.GlueDefs

/-!
# Definitions for the canonicity of `redW`

`RedP l` says that the `ℕ`-word `l` is freely reduced (no two adjacent letters are inverse to one
another), and `decP r hr` decodes a letter `c < 2r` of the `PTCert` word model as a Mathlib
free-group letter `(c / 2, c % 2 == 0)`.
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-- `l` is reduced: no two adjacent letters of `l` are mutually inverse. -/
def RedP (l : List ℕ) : Prop := l.IsChain fun a b => b ≠ a ^^^ 1

/-- Decode a word-model letter `c` as a Mathlib free-group letter: generator `c / 2`, positive
exponent iff `c` is even.  Letters `c` with `c / 2 ≥ r` decode to a default letter. -/
def decP (r : ℕ) (hr : 0 < r) (c : ℕ) : Fin r × Bool :=
  if h : c / 2 < r then (⟨c / 2, h⟩, c % 2 == 0) else (⟨0, hr⟩, true)

end Work.PTCert
