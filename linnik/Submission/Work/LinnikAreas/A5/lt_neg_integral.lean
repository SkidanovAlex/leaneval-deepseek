import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikAreas.A5.lt_weights
import Submission.Work.LinnikAreas.A5.G0_closed

namespace Work.LinnikAreas.A5

open Complex intervalIntegral MeasureTheory
open scoped Interval Topology BigOperators

/-
The values of the two test-function Laplace transforms at the *negative* real point `z = -λ`
(resp. `z = 0`), where they are the integrals `∫₀^K e^{λu} f(u) du` appearing on the right-hand
side of the Chebyshev-ψ (Lambert) input:

* for the normalised weight `f = wc K lam` (`λ > 0`), `∫₀^K e^{λu} wc(u) du = (Ftil K lam (-λ)).re`;
* for the endpoint weight `f = gc K` (`λ = 0`), `∫₀^K gc(u) du = (G0 K 0).re = K/2`.

Proof: `lt_weights` identifies the complex interval integral `∫₀^K e^{-zt} (f t : ℂ) dt` with
`Ftil K lam z` resp. `G0 K z`; at `z = -λ` the exponential is `e^{λt} = ((Real.exp (λ*t) : ℝ) : ℂ)`
so the complex integral is the cast of the real one, and the real part of a cast integral is the
integral of the real parts.  The second conjunct is `G0_closed` plus `∫₀^K (K-t)/K dt = K/2`.
-/
theorem lt_neg_integral (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    (∫ u in (0:ℝ)..K, Real.exp (lam * u) * Work.LinnikAreas.A5.wc K lam u)
        = (Work.LinnikAreas.A5.Ftil K lam (-(lam : ℂ))).re ∧
    (∫ u in (0:ℝ)..K, Work.LinnikAreas.A5.gc K u)
        = (Work.LinnikAreas.A5.G0 K 0).re := by
  constructor
  · -- First conjunct: identify the real integral with the real part of the complex one at z = -λ.
    have hcongr : (∫ u in (0:ℝ)..K, ((Real.exp (lam * u) * wc K lam u : ℝ) : ℂ))
        = ∫ u in (0:ℝ)..K, Complex.exp (-(-(lam : ℂ) * (u : ℂ))) * ((wc K lam u : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      show ((Real.exp (lam * u) * wc K lam u : ℝ) : ℂ)
          = Complex.exp (-(-(lam : ℂ) * (u : ℂ))) * ((wc K lam u : ℝ) : ℂ)
      rw [show -(-(lam : ℂ) * (u : ℂ)) = ((lam * u : ℝ) : ℂ) by push_cast; ring]
      simp only [Complex.ofReal_exp, Complex.ofReal_mul]
    have hre : (∫ u in (0:ℝ)..K, ((Real.exp (lam * u) * wc K lam u : ℝ) : ℂ)).re
        = ∫ u in (0:ℝ)..K, Real.exp (lam * u) * wc K lam u := by
      rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    calc (∫ u in (0:ℝ)..K, Real.exp (lam * u) * wc K lam u)
        = (∫ u in (0:ℝ)..K, ((Real.exp (lam * u) * wc K lam u : ℝ) : ℂ)).re := hre.symm
      _ = (∫ u in (0:ℝ)..K,
              Complex.exp (-(-(lam : ℂ) * (u : ℂ))) * ((wc K lam u : ℝ) : ℂ)).re := by
            rw [hcongr]
      _ = (((Real.sinh (K * lam))⁻¹ : ℂ) * F1 K lam (-(lam : ℂ))).re := by
            rw [integral_exp_mul_wc K lam hK (-(lam : ℂ))]
      _ = (Ftil K lam (-(lam : ℂ))).re := rfl
  · -- Second conjunct: `G0 K 0` is the cast of `∫₀^K gc`, whose real part is that integral.
    have hg := integral_exp_mul_gc K hK 0
    have hsimp : (∫ t in (0:ℝ)..K, Complex.exp (-((0 : ℂ) * (t : ℂ))) * ((gc K t : ℝ) : ℂ))
        = ∫ t in (0:ℝ)..K, ((gc K t : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp
    have hgoal : (G0 K 0).re = ∫ u in (0:ℝ)..K, gc K u := by
      rw [← hg, hsimp, intervalIntegral.integral_ofReal, Complex.ofReal_re]
    exact hgoal.symm

end Work.LinnikAreas.A5
