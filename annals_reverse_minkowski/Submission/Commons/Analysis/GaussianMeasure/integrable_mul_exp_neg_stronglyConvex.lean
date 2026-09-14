import Mathlib
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm
import Submission.Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq

namespace Commons.Analysis.GaussianMeasure

open Filter MeasureTheory
open scoped Topology

/-- If `g := f - π‖·‖²` is convex on all of `E` and `f` is differentiable at `0` with derivative
`L`, then `f` grows at least like `(π/2)‖·‖²`.  The bound is obtained by evaluating the convexity
inequality along the ray `t ↦ t • x` and passing to the limit `t → 0⁺`. -/
private theorem lower_bound_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (L : E →L[ℝ] ℝ) (hL : HasFDerivAt f L 0)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) :
    ∃ c : ℝ, ∀ x : E, f x ≥ Real.pi / 2 * ‖x‖ ^ 2 - c := by
  refine ⟨‖L‖ ^ 2 / (2 * Real.pi) - f 0, fun x => ?_⟩
  have hdir : Tendsto (fun t : ℝ => t⁻¹ * (f (t • x) - f 0)) (𝓝[>] (0 : ℝ)) (𝓝 (L x)) := by
    have h1 : HasDerivAt (fun t : ℝ => t • x) x 0 := by
      simpa using (hasDerivAt_id' (x := (0 : ℝ))).smul_const x
    have hline : HasDerivAt (fun t : ℝ => (0 : E) + t • x) x 0 :=
      (hasDerivAt_const_add_iff (x := (0 : ℝ)) (0 : E)).2 h1
    have hcomp : HasDerivAt (f ∘ fun t : ℝ => (0 : E) + t • x) (L x) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hL hline (by simp)
    simpa [Function.comp_def, zero_add, smul_eq_mul] using hcomp.tendsto_slope_zero_right
  have hconst : Tendsto (fun t : ℝ => f 0 + Real.pi * (1 - t) * ‖x‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (f 0 + Real.pi * ‖x‖ ^ 2)) := by
    have hcont : Continuous (fun t : ℝ => f 0 + Real.pi * (1 - t) * ‖x‖ ^ 2) := by
      continuity
    have h := hcont.tendsto (0 : ℝ)
    rw [show f 0 + Real.pi * (1 - (0 : ℝ)) * ‖x‖ ^ 2 = f 0 + Real.pi * ‖x‖ ^ 2 by ring] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun t : ℝ => t⁻¹ * (f (t • x) - f 0) + f 0 + Real.pi * (1 - t) * ‖x‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (L x + f 0 + Real.pi * ‖x‖ ^ 2)) := by
    simpa only [add_assoc] using hdir.add hconst
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (f (t • x) - f 0) + f 0 + Real.pi * (1 - t) * ‖x‖ ^ 2 ≤ f x := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio 1 by norm_num)] with t ht1 ht0
    have ht0' : 0 < t := ht0
    have ht1' : t < 1 := ht1
    have hnorm : ‖t • x‖ ^ 2 = t ^ 2 * ‖x‖ ^ 2 := by
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hcv := hconv.2 (Set.mem_univ x) (Set.mem_univ (0 : E))
      (le_of_lt ht0') (by linarith) (by ring : t + (1 - t) = 1)
    have hcv' : f (t • x) - Real.pi * ‖t • x‖ ^ 2 ≤
        t * (f x - Real.pi * ‖x‖ ^ 2) + (1 - t) * f 0 := by
      simpa [smul_eq_mul] using hcv
    have hcv'' : f (t • x) - Real.pi * (t ^ 2 * ‖x‖ ^ 2) ≤
        t * (f x - Real.pi * ‖x‖ ^ 2) + (1 - t) * f 0 := by
      rw [hnorm] at hcv'; exact hcv'
    have hkey : f (t • x) - f 0 ≤ (f x - f 0 - Real.pi * (1 - t) * ‖x‖ ^ 2) * t := by
      nlinarith [hcv'']
    have h4 : (f (t • x) - f 0) / t ≤ f x - f 0 - Real.pi * (1 - t) * ‖x‖ ^ 2 :=
      (div_le_iff₀ ht0').mpr hkey
    rw [div_eq_inv_mul] at h4
    linarith [h4]
  have hmain : L x + f 0 + Real.pi * ‖x‖ ^ 2 ≤ f x := le_of_tendsto hlim hle
  have hLx : -(‖L‖ * ‖x‖) ≤ L x := by
    have h1 : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
    have h2 : ‖L x‖ = |L x| := Real.norm_eq_abs (L x)
    have h3 : -(L x) ≤ |L x| := neg_le_abs (L x)
    linarith
  have hquad : -(‖L‖ ^ 2 / (2 * Real.pi)) ≤ L x + Real.pi / 2 * ‖x‖ ^ 2 := by
    have hsq : 0 ≤ (Real.pi * ‖x‖ - ‖L‖) ^ 2 := sq_nonneg _
    have hkey : -(‖L‖ ^ 2) ≤ (Real.pi / 2 * ‖x‖ ^ 2 - ‖L‖ * ‖x‖) * (2 * Real.pi) := by
      nlinarith [hsq]
    have hkey' : -(‖L‖ ^ 2 / (2 * Real.pi)) ≤ Real.pi / 2 * ‖x‖ ^ 2 - ‖L‖ * ‖x‖ := by
      rw [show -(‖L‖ ^ 2 / (2 * Real.pi)) = -(‖L‖ ^ 2) / (2 * Real.pi) by ring]
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr hkey
    linarith
  linarith [hmain, hLx, hquad]

theorem integrable_mul_exp_neg_stronglyConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (f Φ : E → ℝ) (hf : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (hΦc : Continuous Φ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hΦ : ∀ x : E, |Φ x| ≤ C * (1 + ‖x‖) ^ N) : MeasureTheory.Integrable (fun x : E => Φ x * Real.exp (-(f x))) := by
  have hf0 : DifferentiableAt ℝ f 0 := (hf.differentiable (by norm_num)).differentiableAt
  obtain ⟨c, hc⟩ := lower_bound_aux f (fderiv ℝ f 0) hf0.hasFDerivAt hconv
  set K : ℝ := C * Real.exp c with hK
  have hgauss : Integrable
      (fun x : E => (1 + ‖x‖) ^ N * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) :=
    Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq (Real.pi / 2) (by positivity) N
  have hg : Integrable
      (fun x : E => K * ((1 + ‖x‖) ^ N * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2))) :=
    hgauss.const_mul K
  refine hg.mono' ?_ ?_
  · exact (hΦc.mul (Real.continuous_exp.comp (hf.continuous.neg))).aestronglyMeasurable
  · filter_upwards with x
    have hfx : Real.pi / 2 * ‖x‖ ^ 2 - c ≤ f x := hc x
    have hxNnn : 0 ≤ (1 + ‖x‖) ^ N := pow_nonneg (by positivity) N
    have hexp : Real.exp (-(f x)) ≤ Real.exp c * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hfx]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |Φ x| * Real.exp (-(f x))
        ≤ (C * (1 + ‖x‖) ^ N) * (Real.exp c * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) :=
          mul_le_mul (hΦ x) hexp (Real.exp_pos _).le (mul_nonneg hC hxNnn)
      _ = K * ((1 + ‖x‖) ^ N * Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) := by
          rw [hK]; ring

end Commons.Analysis.GaussianMeasure
