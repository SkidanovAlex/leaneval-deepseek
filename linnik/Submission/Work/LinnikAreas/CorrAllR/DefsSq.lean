import Mathlib

/-!
# Digit decomposition of `ZMod (p ^ 2)`

Shared definitions for the local prime-square correlation bound
`Work.LinnikAreas.CorrAllR.corrSumV_sq_good`: every residue modulo `p ^ 2` is uniquely
`r + p * y` with `r, y : ZMod p`.  The map `zmd` is the one whose bijectivity is
`Commons.NumberTheory.DirichletCharacter.zmod_sq_digits_bijective`.
-/

namespace Work.LinnikAreas.CorrAllR

/-- The "digits" map `ZMod p × ZMod p → ZMod (p^2)`, `(r,y) ↦ r + p*y`. -/
def zmd (p : ℕ) [NeZero p] (r y : ZMod p) : ZMod (p ^ 2) :=
  ((r.val : ℕ) : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * ((y.val : ℕ) : ZMod (p ^ 2))

end Work.LinnikAreas.CorrAllR
