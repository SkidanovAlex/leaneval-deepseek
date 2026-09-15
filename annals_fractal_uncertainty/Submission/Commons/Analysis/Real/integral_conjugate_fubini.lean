import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Commons.Analysis.Integral.integral_inv_sq_add

open MeasureTheory Set
open scoped Real

namespace Commons.Analysis.Real

/-- Elementary antiderivative in the `s`-variable of the Poisson kernel:
`∫_0^σ u/(u²+s²) ds = arctan(σ/u)` for `u > 0`. -/
lemma integral_poisson_kernel_s {σ u : ℝ} (hu : 0 < u) :
    (∫ s in (0:ℝ)..σ, u / (u^2 + s^2)) = Real.arctan (σ / u) := by
  have h := Commons.Analysis.Integral.integral_inv_sq_add (k := u) (p := 0) (q := σ) hu
  simpa using h

/-- Fubini exchange for the conjugate Poisson kernel: integrating the conjugate Poisson
transform of `deriv g` in the conjugate variable `s` over `(0, σ)` gives the integral against
`arctan(σ/u)`. -/
theorem integral_conjugate_fubini {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ s in (0:ℝ)..σ, (∫ u in Set.Ioi (0:ℝ), deriv g u * (u / (u^2 + s^2)))
      = ∫ u in Set.Ioi (0:ℝ), deriv g u * Real.arctan (σ / u) := by
  have hcont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hint_deriv : Integrable (deriv g) := hcont.integrable_of_hasCompactSupport hs.deriv
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) σ) with hμ
  set ν : Measure ℝ := volume.restrict (Set.Ioi (0:ℝ)) with hν
  have hF_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => deriv g p.2 * (p.2 / (p.2^2 + p.1^2))) (μ.prod ν) := by fun_prop
  -- The `s`-inner integral is integrable for a.e. `u`
  have hint_s : ∀ᵐ u ∂ν, Integrable (fun s => deriv g u * (u / (u^2 + s^2))) μ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    have haesm : AEStronglyMeasurable (fun s : ℝ => deriv g u * (u / (u^2 + s^2))) μ := by
      apply Continuous.aestronglyMeasurable
      exact continuous_const.mul (continuous_const.div (by continuity) (fun s => by positivity))
    refine Integrable.of_bound haesm (|deriv g u| / u) ?_
    filter_upwards with s
    have hb : (0:ℝ) < u^2+s^2 := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hb, abs_of_pos hu']
    have hle : u / (u^2 + s^2) ≤ 1/u := by
      rw [div_le_iff₀ hb, one_div, inv_mul_eq_div, le_div_iff₀ hu']
      nlinarith [sq_nonneg s]
    calc |deriv g u| * (u / (u ^ 2 + s ^ 2)) ≤ |deriv g u| * (1/u) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = |deriv g u| / u := by rw [mul_one_div]
  -- Domination for the outer `u`-integral
  have hdom : Integrable (fun u : ℝ => (π/2) * |deriv g u|) ν := by
    have h1 : Integrable (fun u : ℝ => ‖deriv g u‖) ν := hint_deriv.norm.restrict
    have h2 := h1.const_mul (π/2)
    simpa only [Real.norm_eq_abs] using h2
  have hG : AEStronglyMeasurable
      (fun q : ℝ × ℝ => ‖deriv g q.1 * (q.1 / (q.1^2 + q.2^2))‖) (ν.prod μ) := by fun_prop
  have hHint_u_meas : AEStronglyMeasurable (fun u => ∫ s, ‖deriv g u * (u/(u^2+s^2))‖ ∂μ) ν :=
    AEStronglyMeasurable.integral_prod_right' (μ := ν) (ν := μ)
      (f := fun q : ℝ × ℝ => ‖deriv g q.1 * (q.1 / (q.1^2 + q.2^2))‖) hG
  have hint_u : Integrable (fun u => ∫ s, ‖deriv g u * (u/(u^2+s^2))‖ ∂μ) ν := by
    refine Integrable.mono' hdom hHint_u_meas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    have hnorm : ‖(∫ s, ‖deriv g u * (u/(u^2+s^2))‖ ∂μ)‖ =
        ∫ s, ‖deriv g u * (u/(u^2+s^2))‖ ∂μ := by
      apply Real.norm_of_nonneg
      apply integral_nonneg
      intro s; apply norm_nonneg
    rw [hnorm]
    have hstep1 : (∫ s, ‖deriv g u * (u/(u^2+s^2))‖ ∂μ) = |deriv g u| * Real.arctan (σ/u) := by
      rw [hμ, ← intervalIntegral.integral_of_le hσ.le]
      have hfun : (fun s : ℝ => ‖deriv g u * (u/(u^2+s^2))‖) =
          (fun s : ℝ => |deriv g u| * (u/(u^2+s^2))) := by
        funext s
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ u/(u^2+s^2))]
      rw [hfun, intervalIntegral.integral_const_mul, integral_poisson_kernel_s hu']
    rw [hstep1]
    calc |deriv g u| * Real.arctan (σ/u) ≤ |deriv g u| * (π/2) :=
          mul_le_mul_of_nonneg_left (le_of_lt (Real.arctan_lt_pi_div_two _)) (abs_nonneg _)
      _ = (π/2) * |deriv g u| := by ring
  have hIntegrable : Integrable
      (fun p : ℝ × ℝ => deriv g p.2 * (p.2 / (p.2^2 + p.1^2))) (μ.prod ν) :=
    (integrable_prod_iff' hF_meas).mpr ⟨hint_s, hint_u⟩
  have hInt' : Integrable
      (fun p : ℝ × ℝ => deriv g p.2 * (p.2 / (p.2^2 + p.1^2)))
      ((volume.restrict (Set.uIoc (0:ℝ) σ)).prod ν) := by
    rw [Set.uIoc_of_le hσ.le]
    simpa only [hμ] using hIntegrable
  have hswap := intervalIntegral_integral_swap (μ := ν) (a := (0:ℝ)) (b := σ)
      (f := fun s u => deriv g u * (u / (u^2 + s^2))) hInt'
  have hswap' : (∫ s in (0:ℝ)..σ, (∫ u, deriv g u * (u / (u^2 + s^2)) ∂(volume.restrict (Set.Ioi (0:ℝ)))))
      = ∫ u, (∫ s in (0:ℝ)..σ, deriv g u * (u / (u^2 + s^2))) ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
    simpa only [hν] using hswap
  rw [hν, hswap']
  have hinner : (fun u => ∫ s in (0:ℝ)..σ, deriv g u * (u / (u^2 + s^2)))
      =ᵐ[volume.restrict (Set.Ioi (0:ℝ))] (fun u => deriv g u * Real.arctan (σ/u)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    rw [intervalIntegral.integral_const_mul, integral_poisson_kernel_s hu']
  rw [integral_congr_ae hinner]

end Commons.Analysis.Real