import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.KMTPlan.A6

open MeasureTheory

/-- The character `e(x) = exp(2πix)` takes values of modulus one. -/
private lemma norm_ee_eq_one (x : ℝ) : ‖Work.KMTAreas.A7.ee x‖ = 1 := by
  have h : Work.KMTAreas.A7.ee x
      = Complex.exp ((((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I) := by
    simp only [Work.KMTAreas.A7.ee]
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- **Marginal integrability of the model Fubini integrand.**

For integrable measurable amplitudes `a`, `b : ℝ → ℂ`, measurable phases `u`, `v : ℝ → ℝ` and a
weight `W : ℝ → ℂ` integrable on `(1/2,1]`, the marginal in `z = (z₁,z₂)` of the Fubini integrand
`(t,z) ↦ W t · (a z₁ e(u t z₁)) · (b z₂ e(v t z₂))` is integrable on `ℝ²`.

This is the integrability input that lets the double integrals of the §6 model approximation be
split (`Work.KMTPlan.A6.MdlCwIntegIdent`): the integrand is dominated by
`(‖a z₁‖ ‖b z₂‖) ‖W t‖`, which is a product of an integrable function of `z` and an integrable
function of `t`, so Tonelli (`MeasureTheory.Integrable.integral_prod_left`) gives the marginal. -/
theorem MarginalModInt {a b : ℝ → ℂ} (ha : MeasureTheory.Integrable a) (hb : MeasureTheory.Integrable b)
    (ham : Measurable a) (hbm : Measurable b) {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v)
    {W : ℝ → ℂ} (hW : MeasureTheory.Integrable W (MeasureTheory.volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
    (hWm : Measurable W) :
    MeasureTheory.Integrable (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
        W t * (a z.1 * Work.KMTAreas.A7.ee (u t * z.1)) * (b z.2 * Work.KMTAreas.A7.ee (v t * z.2)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- The dominating function factorises in `(z, t)`.
  have hG : Integrable (fun z : ℝ × ℝ => ‖a z.1‖ * ‖b z.2‖) (volume.prod volume) :=
    ha.norm.mul_prod hb.norm
  have hWn : Integrable (fun t : ℝ => ‖W t‖) (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := hW.norm
  -- The pointwise modulus identity.
  have hbound : ∀ (t ξ₁ ξ₂ : ℝ),
      ‖W t * (a ξ₁ * Work.KMTAreas.A7.ee (u t * ξ₁))
        * (b ξ₂ * Work.KMTAreas.A7.ee (v t * ξ₂))‖ = (‖a ξ₁‖ * ‖b ξ₂‖) * ‖W t‖ := by
    intro t ξ₁ ξ₂
    simp only [norm_mul, norm_ee_eq_one, mul_one]
    ring
  -- Integrability of the integrand in the `(z, t)` order.
  have hLR : Integrable (fun w : (ℝ × ℝ) × ℝ =>
      W w.2 * (a w.1.1 * Work.KMTAreas.A7.ee (u w.2 * w.1.1))
        * (b w.1.2 * Work.KMTAreas.A7.ee (v w.2 * w.1.2)))
      ((volume.prod volume).prod (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) := by
    refine (hG.mul_prod hWn).mono' ?_ ?_
    · simp only [Work.KMTAreas.A7.ee]; fun_prop
    · filter_upwards with w
      exact le_of_eq (hbound w.2 w.1.1 w.1.2)
  -- Marginalise: the `t`-integral of the integrand is integrable in `z`.
  have hmarg : Integrable (fun z : ℝ × ℝ =>
      ∫ t, W t * (a z.1 * Work.KMTAreas.A7.ee (u t * z.1))
        * (b z.2 * Work.KMTAreas.A7.ee (v t * z.2))
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) (volume.prod volume) :=
    hLR.integral_prod_left
  -- Convert the restricted-measure integral to the interval integral.
  have hpt : (fun z : ℝ × ℝ => ∫ t in (1 / 2 : ℝ)..1,
        W t * (a z.1 * Work.KMTAreas.A7.ee (u t * z.1))
          * (b z.2 * Work.KMTAreas.A7.ee (v t * z.2)))
      = fun z : ℝ × ℝ => ∫ t,
        W t * (a z.1 * Work.KMTAreas.A7.ee (u t * z.1))
          * (b z.2 * Work.KMTAreas.A7.ee (v t * z.2))
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    funext z
    rw [intervalIntegral.integral_of_le hle]
  rw [hpt]
  exact hmarg

end Work.KMTPlan.A6
