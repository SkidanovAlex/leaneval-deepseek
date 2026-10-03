/-
# Definitions for the §17 Plancherel estimate `sumChiNormUniSCharSq`

`Work.FIArea7.uniSChar Pa Q ε β k χ = Σ_{z ∈ gBox (radN Pa)} unitCoeff Q (uniCoeff ε β k) z ·
χ(unitClassD Q z)` is the character sum (17.12).  Because the factor `unitCoeff Q c z =
conj(c z)·[z unit mod Q]` vanishes off the units, this sum only sees the box points `z` that are
units modulo `Q`, and it is the Fourier transform over `G = (ℤ[i]/Q)^*` of the class function

  `uniClassFn Pa Q c a = Σ_{z : unitClassD Q z = a} conj(c z)`

(this is `Work.FIArea7.uniSChar_eq_sum_uniClassFn`).  The present file only fixes those two
notions, so that the estimtes about them can be stated independently of the final assembly.
-/
import Mathlib
import Submission.Work.FIArea7.Section16Expansion

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The box `gBox (radN Pa)` restricted to the Gaussian integers that are units modulo `Q`: the
support of the coefficient `unitCoeff Q c`. -/
def uniUnitBox (Pa : Work.FITop.Params) (Q : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q)

/-- **The class function whose Fourier transform is `uniSChar`**: at the class
`a ∈ G = (ℤ[i]/Q)^*` it is the sum of `conj (c z)` over the box points that are units modulo `Q`
and lie in the class `a`. -/
def uniClassFn (Pa : Work.FITop.Params) (Q : ℕ) (c : GaussianInt → ℂ) (a : GaussUnit Q) : ℂ :=
  ∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), star (c z)

end

end Work.FIArea7
