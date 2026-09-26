import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.shift_helpers

namespace Work.CKFinal.LineDecay

/-!
# `P₃` as a combination of the three tail integrals `∫_{t>1} A_ε`

The tail piece of the shifted representation is
`P₃(K) r τ = ∫_{t ≥ 1} Φ(K)(τ,t)·e^{-λt} dt` with
`Φ(K)(τ,t) = 2K(τ,it) - K(τ,it-1) - K(τ,it+1)` (`Work.CKFinal.Phi`) and `λ = πr²`
(`Work.Asymptotics.gaussWeight r t = e^{-λt}`).

Since the three "ray" integrands are
`A₀ = Kax K τ 0 · gw`, `A₋ = Kax K τ (-1) · gw`, `A₊ = Kax K τ 1 · gw`
(`A0fun`, `Amfun`, `Apfun`), the integrand of `P₃` is *pointwise*
`2A₀ - A₋ - A₊`, and `∫_{t ≥ 1}` may be replaced by `∫_{t > 1}` because the two sets differ by the
null set `{1}`.  Linearity of the Bochner integral over `ℂ` then gives the stated identity, the
integrability hypotheses being exactly what `integral_sub`/`integral_const_mul` require on `Ioi 1`.

This is the elementary bookkeeping step used when `P₃` is bounded by summing the three
exponentially decaying tail estimates `∫_{t>1} A_ε`.
-/

/-- The integrand of `P₃` is the second difference `2A₀ - A₋ - A₊` of the three tail integrands. -/
theorem Phi_mul_gaussWeight_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) (r : ℝ) (t : ℝ) :
    Work.CKFinal.Phi (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t
      = 2 * A0fun ℓ d τ r t - Amfun ℓ d τ r t - Apfun ℓ d τ r t := by
  simp only [Work.CKFinal.Phi, A0fun, Amfun, Apfun]
  ring

/-- `P₃` written with the second difference of the three tail integrands, integrated on `Ioi 1`. -/
theorem P3_eq_integral_Ioi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) (r : ℝ) :
    Work.CKFinal.P3 (Work.Kernels.Kfun ℓ d) r τ
      = ∫ t in Set.Ioi 1, (2 * A0fun ℓ d τ r t - Amfun ℓ d τ r t - Apfun ℓ d τ r t) := by
  rw [show Work.CKFinal.P3 (Work.Kernels.Kfun ℓ d) r τ
      = ∫ t in Set.Ici (1 : ℝ),
          Work.CKFinal.Phi (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t from
    rfl]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun t => Phi_mul_gaussWeight_eq ℓ d τ r t)

theorem P3_eq_two_B0_sub_Bm_sub_Bp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) (r : ℝ)
    (hA0 : MeasureTheory.IntegrableOn (Work.CKFinal.LineDecay.A0fun ℓ d τ r) (Set.Ioi 1))
    (hAm : MeasureTheory.IntegrableOn (Work.CKFinal.LineDecay.Amfun ℓ d τ r) (Set.Ioi 1))
    (hAp : MeasureTheory.IntegrableOn (Work.CKFinal.LineDecay.Apfun ℓ d τ r) (Set.Ioi 1)) :
    Work.CKFinal.P3 (Work.Kernels.Kfun ℓ d) r τ
      = 2 * (∫ t in Set.Ioi 1, Work.CKFinal.LineDecay.A0fun ℓ d τ r t)
        - (∫ t in Set.Ioi 1, Work.CKFinal.LineDecay.Amfun ℓ d τ r t)
        - (∫ t in Set.Ioi 1, Work.CKFinal.LineDecay.Apfun ℓ d τ r t) := by
  have hI0 : MeasureTheory.Integrable (fun t => 2 * A0fun ℓ d τ r t)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := hA0.const_mul 2
  have hI1 : MeasureTheory.Integrable
      (fun t => 2 * A0fun ℓ d τ r t - Amfun ℓ d τ r t)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := hI0.sub hAm
  rw [P3_eq_integral_Ioi,
    MeasureTheory.integral_sub hI1 hAp, MeasureTheory.integral_sub hI0 hAm,
    MeasureTheory.integral_const_mul]

end Work.CKFinal.LineDecay
