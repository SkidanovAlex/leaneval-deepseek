import ChallengeDeps
import Submission.Work.BoseBogFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-!
# The explicit value of the LHY error `ε(μ,ρ_z)` at FS's parameter choice

`Work.BoseB6.lhyEps` is FS's `eq:LebesgueError-Total` display

    ε = (μa)^{1/4}√R + ε_T
        + (K_ℓ s)⁻¹(1 + log d⁻¹ + log(K_ℓ d s/(μa³)^{1/2}))
        + ε_T(K_ℓ d s)⁻¹(1 + log(K_ℓ d s/(μa³)^{1/2}))

At FS's parameter choice (`Work.BoseBox.fsParams` of the diluteness `μa³`,
`X = (μa³)^{1/323}`, `s = X`, `d = X⁶`, `ε_T = X^{23/4}`, `K_ℓ = X^{-3/2}`, entry
through `Work.BoseBox.paramsAt`) every factor is a monomial in the diluteness
`D = μa³`:

* `ε_T = D^{23/1292}`, `K_ℓ s = D^{-1/646}`, `K_ℓ d s = D^{11/646}`, `d = D^{6/323}`,
* `(μa³)^{1/2} = D^{1/2}`,

so the logarithms collapse to multiples of `log D = -log(1/D)`:

* `log d⁻¹ = log D^{-6/323} = -(6/323) log D`,
* `log(K_ℓ d s/D^{1/2}) = log D^{11/646 - 1/2} = -(156/323) log D`,

and the display becomes the closed form of `lhyEps_explicit` below.

The `rpow` bookkeeping is done in `lhyEps_diluteness`; the theorem then only
unfolds the parameter block.
-/

/-- The explicit evaluation of `lhyEps` at FS's parameter monomials in the
diluteness `D = μ a³`.  This is `lhyEps_explicit` with the parameter block already
unfolded (so that the right-hand side is a function of `μ`, `a`, `R` only). -/
theorem lhyEps_diluteness (a R μ : ℝ) (ha : 0 < a) (hμ : 0 < μ) :
    Work.BoseB6.lhyEps a R ((μ * a ^ 3) ^ ((23 : ℝ) / 1292))
        ((μ * a ^ 3) ^ (-((3 : ℝ) / 646)))
        ((μ * a ^ 3) ^ ((1 : ℝ) / 323))
        ((μ * a ^ 3) ^ ((6 : ℝ) / 323)) μ
      = (μ * a) ^ ((1 : ℝ) / 4) * Real.sqrt R
        + (μ * a ^ 3) ^ ((23 : ℝ) / 1292)
        + (μ * a ^ 3) ^ ((1 : ℝ) / 646)
            * (1 + ((162 : ℝ) / 323) * Real.log (1 / (μ * a ^ 3)))
        + (μ * a ^ 3) ^ ((1 : ℝ) / 1292)
            * (1 + ((156 : ℝ) / 323) * Real.log (1 / (μ * a ^ 3))) := by
  have hK : 0 < μ * a ^ 3 := by positivity
  have hlog1K : Real.log (1 / (μ * a ^ 3)) = -Real.log (μ * a ^ 3) := by
    rw [one_div, Real.log_inv]
  unfold Work.BoseB6.lhyEps
  simp only [hlog1K]
  -- collapse the products of powers of `D = μ a³` into single powers
  rw [← Real.rpow_add hK]
  rw [← Real.rpow_add hK]
  rw [← Real.rpow_add hK]
  -- exponent arithmetic
  rw [show (-((3 : ℝ) / 646) + 1 / 323 : ℝ) = -((1 : ℝ) / 646) from by norm_num]
  rw [show (-((3 : ℝ) / 646) + 6 / 323 + 1 / 323 : ℝ) = 11 / 646 from by norm_num]
  -- turn the inverses into negative powers
  simp only [← Real.rpow_neg hK.le, neg_neg]
  -- turn the quotients into differences of exponents
  simp only [← Real.rpow_sub hK]
  -- merge the remaining product
  rw [← Real.rpow_add hK]
  rw [show ((23 : ℝ) / 1292 + -((11 : ℝ) / 646)) = 1 / 1292 from by norm_num]
  rw [show ((11 : ℝ) / 646 - 1 / 2) = -((156 : ℝ) / 323) from by norm_num]
  -- `log D^y = y log D` for the three remaining logarithms
  simp only [Real.log_rpow hK]
  ring

theorem lhyEps_explicit (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
      = (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R
        + (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292)
        + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
            * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
        + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
            * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) := by
  -- unfold the parameter block: every parameter is `fsXp (μ a³) c = (μ a³)^{c/323}`
  simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp,
    Work.BoseFixR.dil]
  -- normalise the two non-trivial exponents of `fsXp`
  rw [show (((23 : ℝ) / 4) / 323 : ℝ) = (23 : ℝ) / 1292 from by norm_num]
  rw [show ((-((3 : ℝ) / 2)) / 323 : ℝ) = -((3 : ℝ) / 646) from by norm_num]
  exact lhyEps_diluteness (_root_.BoseGases.a v) R μ hav hμ

end Work.BoseBogFS
