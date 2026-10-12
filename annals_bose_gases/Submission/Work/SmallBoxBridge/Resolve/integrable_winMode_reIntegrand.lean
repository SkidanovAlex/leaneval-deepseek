import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxBridge.Resolve

open MeasureTheory

/-- Integrability of the `p`-integrand `F(‖p‖)·|∫_y e^{−i⟪p,y⟫}g(y)dy|²` of the windowed
mode form.  The inner `y`-integral `A p = ∫_y e^{−i⟪p,y⟫}g(y)dy` is bounded uniformly in `p`
by `C = ∫_y |g(y)|dy` (the exponential has modulus one), and `A` is a.e. strongly measurable
as the Bochner integral of a jointly measurable family.  Hence the integrand is dominated by
`|F(‖p‖)|·C²`, which is integrable because `p ↦ F(‖p‖)` is. -/
theorem integrable_winMode_reIntegrand {F : ℝ → ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ((F ‖p‖ : ℝ) : ℂ) *
      ((∫ y : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ)) *
       (starRingEnd ℂ) (∫ y : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ))))
      MeasureTheory.volume := by
  classical
  set A : EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun p => ∫ y : EuclideanSpace ℝ (Fin 3),
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ) with hAdef
  set C : ℝ := ∫ y : EuclideanSpace ℝ (Fin 3), ‖g y‖ with hCdef
  have hCnonneg : 0 ≤ C := by
    rw [hCdef]; exact integral_nonneg (fun y => norm_nonneg _)
  -- uniform bound on the inner `y`-integral
  have hAge : ∀ p : EuclideanSpace ℝ (Fin 3), ‖A p‖ ≤ C := by
    intro p
    have hmain : ‖∫ y : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ)‖
        ≤ ∫ y : EuclideanSpace ℝ (Fin 3), ‖g y‖ := by
      calc ‖∫ y : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ)‖
          ≤ ∫ y : EuclideanSpace ℝ (Fin 3),
              ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ y : EuclideanSpace ℝ (Fin 3), ‖g y‖ := by
            apply integral_congr_ae
            filter_upwards with y
            rw [norm_mul]
            have harg : -(Complex.I * (inner ℝ p y : ℂ))
                = Complex.I * ((-(inner ℝ p y) : ℝ) : ℂ) := by
              push_cast; ring
            rw [harg, Complex.norm_exp_I_mul_ofReal, one_mul]
            rw [Real.norm_eq_abs]; exact RCLike.norm_ofReal (g y)
    simpa only [hAdef, hCdef] using hmain
  -- a.e. strong measurability of `A`
  have hAmeas : AEStronglyMeasurable A volume := by
    have hjoint : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ z.1 z.2 : ℂ))) * (g z.2 : ℂ))
        (volume.prod volume) := by
      have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ z.1 z.2 : ℂ)))) := by
        have h1 : Continuous (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            inner ℝ z.1 z.2) := continuous_inner
        exact Complex.continuous_exp.comp
          (((continuous_const.mul (Complex.continuous_ofReal.comp h1)).neg))
      exact hc.stronglyMeasurable.aestronglyMeasurable.mul
        (hg.ofReal.aestronglyMeasurable.comp_snd)
    have key := AEStronglyMeasurable.integral_prod_right' hjoint
    rw [hAdef]
    exact key
  -- a.e. strong measurability of the full integrand
  have htarget_meas : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) =>
        ((F ‖p‖ : ℝ) : ℂ) * (A p * (starRingEnd ℂ) (A p))) volume := by
    exact (hF.ofReal.aestronglyMeasurable).mul (hAmeas.mul hAmeas.star)
  -- the dominating integrable function `|F(‖p‖)|·C²`
  have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖F ‖p‖‖ * (C * C)) volume :=
    hF.norm.mul_const (C * C)
  refine Integrable.mono' hdom htarget_meas ?_
  filter_upwards with p
  have h1 : ‖((F ‖p‖ : ℝ) : ℂ)‖ = ‖F ‖p‖‖ := by
    rw [Real.norm_eq_abs]; exact RCLike.norm_ofReal (F ‖p‖)
  rw [norm_mul, norm_mul, Complex.norm_conj, h1]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (hAge p) (hAge p) (norm_nonneg _) hCnonneg) (norm_nonneg _)

end Work.SmallBoxBridge.Resolve
