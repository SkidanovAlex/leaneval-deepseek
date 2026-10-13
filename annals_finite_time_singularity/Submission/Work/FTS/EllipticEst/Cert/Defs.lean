/-
Copyright: work module for the Elgindi finite-time singularity project.

# Shared vocabulary for the open-quadrant certificate `F_*(F)·sin 2θ ∈ ℋ^k`

The target of this directory is the certificate

  `Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin`:
`F_*(F)·sin 2θ ∈ ℋ^k` for the source `F` of a solution `Ψ` of the elliptic problem
(`Work.FTS.EllipticEst.EllHyp α k F Ψ`, `0 < α ≤ 1/4`).

The source `F` of `EllHyp` is *not* smooth on a neighbourhood of the closed quadrant: it is
only known to equal `bslOp α Ψ` on the open quadrant and, because Lean's `Real.tan` is
totalised (`Real.tan (π/2) = 0`), the function `z ↦ bslOp α Ψ z θ` genuinely jumps at
`θ = π/2` (see the audit note in `Submission/Work/FTS/EllipticEst/alphaDzW_Hk_le.lean`).
The certificate therefore has to be proved in the *open-quadrant* class `SmoothOpen` of
`Submission/Work/FTS/EllipticEst/OpenQDefs.lean`, and — since the `ℋ^k`-membership of
`F_*(F)·sin 2θ` is expressed through the norms of `Work.Spaces`, whose integrands involve
`deriv` — the *explicit* form of the integrand is needed.

## The separated form

Write `g z θ = R(z)·sin 2θ`.  Since `D_z` only sees the radial factor and `D_θ` only the
angular one (`Work.FTS.EllipticEst.DzIter_fstarSin_eq`,
`Work.FTS.EllipticEst.mixed_fstarSin_eq`), the `ℋ^k`-integrand of `g` is

  `HkIntegrand α k g z θ
     = ∑_{i≤k} (radIter R i z)² w(z)² sin(2θ)^{2-η}
       + ∑_{i,j≤k} [1 ≤ i, i+j ≤ k] (radIter R j z)² w(z)² (D_θ^i(sin 2θ))² sin(2θ)^{-γ}`,

with `w(z) = (1+z)²/z²` the radial weight and `γ = gam α = 1 + α/10` the angular exponent.
That is the definition `HkExp` below, whose angular factors are `angZ` and `angA`.

The point of the separated form is that the `θ`-integral of `HkExp α k R z ·` is a finite
combination of the *constants* `∫_θ sin(2θ)^{2-η}` and `∫_θ angA α i` with coefficients
`(radIter R j z)² w(z)²`; this is what makes the slice integral `z ↦ ∫_θ HkIntegrand α k g z θ`
accessible (`integral_HkExp`), and hence its a.e. strong measurability and integrability.

Everything in this module is definitional.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.OpenQAng

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false

/-- `angZ θ = sin(2θ)^{2-η}`: the angular factor of a pure `D_z`-summand of the
`ℋ^k`-integrand of a function of the separated form `R(z)·sin 2θ`.

`2 - η = 101/100 > 0`, so `angZ` is continuous on `ℝ` and bounded by `1` on `Iθ`. -/
def angZ (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)

/-- `angA α i θ = (D_θ^i(sin 2θ))² · sin(2θ)^{-γ}`, `γ = gam α`: the angular factor of a
mixed summand of the `ℋ^k`-integrand of a function of the separated form `R(z)·sin 2θ`.
It is comparable to `angZ`: on `Iθ` it is bounded by the constant `angK i` of
`Work.FTS.EllipticEst.FstarHkOpen` (`angK_bound`), for every `γ ∈ [1,2]`. -/
def angA (α : ℝ) (i : ℕ) (θ : ℝ) : ℝ :=
  (Work.FTS.EllipticEst.sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- **The `ℋ^k`-integrand of a separated function `R(z)·sin 2θ`**, with the radial factor
expressed through the iterates `radIter R i` of `R` (`radIter R i z = (D_z^i R)(z)`):

  `HkExp α k R z θ
     = ∑_{i≤k} (radIter R i z)² w(z)² angZ θ
       + ∑_{i,j≤k} [1 ≤ i, i+j ≤ k] (radIter R j z)² w(z)² angA α i θ`.

`HkIntegrand_radial_sin` identifies it with `HkIntegrand α k (fun z θ => R z * sin 2θ)`. -/
def HkExp (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
        else 0

end Work.FTS.EllipticEst.Cert
