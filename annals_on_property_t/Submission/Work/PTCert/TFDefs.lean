import Mathlib
import Submission.Work.PTCert.Math

/-!
# Definitions for the twisted Fourier criterion

`WSfun` is the Fourier-twisted bilinear form
`W_S(x,y) = Σ_a χ_S(a) · sgn_a(y) · M x (act a y)` appearing in the statement of
`Submission.PTCert.TwistedFourierCriterion`, and `cSfun` is the twisted Fourier
coefficient of a vector `v` attached to an orbit representative.
-/

open OnPropertyT Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

namespace Submission.PTCert

/-- The Fourier-twisted bilinear form of `TwistedFourierCriterion`:
`W_S(x,y) = Σ_a χ_S(a) · sgn a y · M x (act a y)`. -/
noncomputable def WSfun {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (sgn : (Fin m → ZMod 2) → ι → ℝ) (M : Matrix ι ι ℝ) (S : Finset (Fin m))
    (x y : ι) : ℝ :=
  ∑ a, chiS S a * sgn a y * M x (act a y)

/-- The twisted Fourier coefficient of a vector `v` at a representative `xb`:
`c_S(xb) = Σ_{x : rep x = xb} v x · χ_S(nu x) · sgn (nu x) xb`. -/
noncomputable def cSfun {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (sgn : (Fin m → ZMod 2) → ι → ℝ) (nu : ι → (Fin m → ZMod 2))
    (rep : ι → ι) (S : Finset (Fin m)) (xb : ι) : ℝ :=
  ∑ x : {x : ι // rep x = xb}, v x.1 * chiS S (nu x.1) * sgn (nu x.1) xb

end Submission.PTCert
