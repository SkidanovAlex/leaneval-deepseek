import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.cauchyTransform_eq_unsub

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal Topology
open MeasureTheory Set

/-- Translation/support step: if `f` is supported in the disc of radius `ρ/2` and `‖z‖ < ρ/2`,
the difference-quotient integral against the Cauchy kernel equals the integral against
`(ζ - z)⁻¹` over the fixed disc `‖ζ‖ < ρ`.  `∂̄f` vanishes off `‖ζ‖ ≤ ρ/2` (a `C¹` function
vanishing on an open set has vanishing differential there), and
`Metric.ball 0 (ρ/2) ⊆ Metric.ball 0 ρ ∩ Metric.ball z ρ`, so all balls may be replaced by `univ`
up to null sets.  Use `Work.CR.Flat.Cauchy.integral_inv_ball` (`∫_{‖w‖<ρ} w⁻¹ = 0`) to kill the
constant term `∂̄f z / w`, and `MeasureTheory.integral_add_left_eq_self` for `ζ = z + w`. -/
theorem integral_dbarC_translate {ρ : ℝ} (hρ : 0 < ρ) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : Work.CR.Flat.SupportedInBall (ρ / 2) f) {z : ℂ} (hz : ‖z‖ < ρ / 2) :
    ∫ w in Metric.ball (0 : ℂ) ρ, (Work.CR.Flat.dbarC f (z + w) - Work.CR.Flat.dbarC f z) / w
      = ∫ ζ in Metric.ball (0 : ℂ) ρ, (Work.CR.Flat.dbarC f ζ) / (ζ - z) := by
  -- `∂̄f` vanishes strictly outside the disc of radius `ρ/2`: `f` is `C¹` and vanishes on the
  -- open set `{ρ/2 < ‖ζ‖}`, so its differential (and hence `∂̄f`) vanishes there too.
  have hdbar_zero : ∀ ζ : ℂ, ρ / 2 < ‖ζ‖ → dbarC f ζ = 0 := by
    intro ζ hζ
    have hopen : IsOpen {x : ℂ | ρ / 2 < ‖x‖} :=
      isOpen_lt (continuous_const : Continuous fun _ : ℂ => ρ / 2) continuous_norm
    have hf0 : f =ᶠ[𝓝 ζ] (fun _ : ℂ => (0 : ℂ)) := by
      filter_upwards [hopen.mem_nhds hζ] with x hx
      exact hfsupp x (le_of_lt hx)
    have hderiv : fderiv ℝ f ζ = 0 := by
      have h1 : HasFDerivAt f (0 : ℂ →L[ℝ] ℂ) ζ :=
        (hasFDerivAt_const (0 : ℂ) ζ).congr_of_eventuallyEq hf0
      simpa using h1.fderiv
    simp [dbarC, hderiv]
  -- consequently `w ↦ ∂̄f (z + w)` is supported in the disc `‖w‖ < ρ`
  have hA_zero : ∀ w : ℂ, ρ ≤ ‖w‖ → dbarC f (z + w) = 0 := by
    intro w hw
    refine hdbar_zero _ ?_
    have h1 : ‖w‖ ≤ ‖z + w‖ + ‖z‖ := by
      have h := norm_sub_le (z + w) z
      rwa [add_sub_cancel_left] at h
    linarith
  -- continuity of `w ↦ ∂̄f (z + w)`
  have hAcont : Continuous fun w : ℂ => dbarC f (z + w) := by
    have hd : Continuous fun ζ : ℂ => fderiv ℝ f ζ := hf.continuous_fderiv one_ne_zero
    unfold dbarC
    fun_prop
  -- integrability of both pieces of the split integrand on `‖w‖ < ρ`
  have hintA : IntegrableOn (fun w : ℂ => dbarC f (z + w) * w⁻¹) (Metric.ball 0 ρ) :=
    ((LocallyIntegrable.continuous_mul hAcont locallyIntegrable_inv_complex).integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) ρ)).mono_set Metric.ball_subset_closedBall
  have hintC : IntegrableOn (fun w : ℂ => dbarC f z * w⁻¹) (Metric.ball 0 ρ) :=
    (integrableOn_inv_ball ρ).const_mul (dbarC f z)
  -- split the difference quotient and kill the constant term with `∫ w⁻¹ = 0`
  have hsplit : ∫ w in Metric.ball (0 : ℂ) ρ, (dbarC f (z + w) - dbarC f z) / w
      = (∫ w in Metric.ball (0 : ℂ) ρ, dbarC f (z + w) * w⁻¹)
        - (∫ w in Metric.ball (0 : ℂ) ρ, dbarC f z * w⁻¹) := by
    rw [show (fun w : ℂ => (dbarC f (z + w) - dbarC f z) / w)
        = fun w : ℂ => dbarC f (z + w) * w⁻¹ - dbarC f z * w⁻¹ from by
      funext w; rw [div_eq_mul_inv, sub_mul]]
    exact integral_sub hintA hintC
  have hconst : ∫ w in Metric.ball (0 : ℂ) ρ, dbarC f z * w⁻¹ = 0 := by
    rw [integral_const_mul, integral_inv_ball ρ, mul_zero]
  -- the term `w ↦ ∂̄f (z + w) / w` is supported in the disc, so the ball integral is a full one
  have hsupp_int : ∫ w in Metric.ball (0 : ℂ) ρ, dbarC f (z + w) * w⁻¹
      = ∫ w : ℂ, dbarC f (z + w) * w⁻¹ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have hwρ : ρ ≤ ‖w‖ := by
      have h : ¬ dist (0 : ℂ) w < ρ := by simpa [Metric.mem_ball] using hw
      simpa [dist_eq_norm] using not_lt.mp h
    rw [hA_zero w hwρ, zero_mul]
  -- translation `ζ = z + w`
  have htrans : ∫ w : ℂ, dbarC f (z + w) * w⁻¹ = ∫ ζ : ℂ, dbarC f ζ * (ζ - z)⁻¹ := by
    have h := integral_add_left_eq_self (μ := (volume : Measure ℂ))
      (fun ζ : ℂ => dbarC f ζ * (ζ - z)⁻¹) z
    simpa [add_sub_cancel_left] using h
  -- and `ζ ↦ ∂̄f ζ / (ζ - z)` is supported in the disc as well
  have hsupp_int2 : ∫ ζ : ℂ, dbarC f ζ * (ζ - z)⁻¹
      = ∫ ζ in Metric.ball (0 : ℂ) ρ, dbarC f ζ * (ζ - z)⁻¹ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ζ hζ
    have hζρ : ρ ≤ ‖ζ‖ := by
      have h : ¬ dist (0 : ℂ) ζ < ρ := by simpa [Metric.mem_ball] using hζ
      simpa [dist_eq_norm] using not_lt.mp h
    rw [hdbar_zero ζ (by linarith), zero_mul]
  have hfinal : ∫ ζ in Metric.ball (0 : ℂ) ρ, dbarC f ζ * (ζ - z)⁻¹
      = ∫ ζ in Metric.ball (0 : ℂ) ρ, dbarC f ζ / (ζ - z) := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro ζ _
    simp only [div_eq_mul_inv]
  calc ∫ w in Metric.ball (0 : ℂ) ρ, (dbarC f (z + w) - dbarC f z) / w
      = (∫ w in Metric.ball (0 : ℂ) ρ, dbarC f (z + w) * w⁻¹)
        - (∫ w in Metric.ball (0 : ℂ) ρ, dbarC f z * w⁻¹) := hsplit
    _ = ∫ w in Metric.ball (0 : ℂ) ρ, dbarC f (z + w) * w⁻¹ := by rw [hconst, sub_zero]
    _ = ∫ w : ℂ, dbarC f (z + w) * w⁻¹ := hsupp_int
    _ = ∫ ζ : ℂ, dbarC f ζ * (ζ - z)⁻¹ := htrans
    _ = ∫ ζ in Metric.ball (0 : ℂ) ρ, dbarC f ζ * (ζ - z)⁻¹ := hsupp_int2
    _ = ∫ ζ in Metric.ball (0 : ℂ) ρ, dbarC f ζ / (ζ - z) := hfinal

end Work.CR.Flat.Cauchy
