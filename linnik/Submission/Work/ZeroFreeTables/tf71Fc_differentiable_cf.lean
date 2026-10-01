import Mathlib
import Submission.Work.ZeroFreeTables.tf71Fc_model
import Submission.Work.ZeroFreeTables.testFn71_defs

namespace Work.ZeroFreeTables

open MeasureTheory intervalIntegral

theorem tf71Fc_differentiable_cf (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) :
    Differentiable ℂ (fun z : ℂ => ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
      Complex.exp (-(z * (t:ℂ))) * Work.ZeroFreeTables.tf71cfC θ lam t) := by
  set b : ℝ := 2 * tf71γ θ lam with hb
  have hbpos : 0 < b := by
    rw [hb]; exact tf71_twoγ_pos hθ0 hθ1 hlam
  have hbnonneg : 0 ≤ b := le_of_lt hbpos
  have hcontF : ∀ x : ℂ, Continuous
      (fun t : ℝ => Complex.exp (-(x * (t:ℂ))) * tf71cfC θ lam t) := by
    intro x
    have h1 : Continuous (fun t : ℝ => Complex.exp (-(x * (t:ℂ)))) :=
      Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
    exact h1.mul (tf71cfC_cont θ lam)
  have hcontF' : ∀ x : ℂ, Continuous
      (fun t : ℝ => Complex.exp (-(x * (t:ℂ))) * (-(t:ℂ)) * tf71cfC θ lam t) := by
    intro x
    have h1 : Continuous (fun t : ℝ => Complex.exp (-(x * (t:ℂ))) * (-(t:ℂ))) :=
      (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)).mul
        Complex.continuous_ofReal.neg
    exact h1.mul (tf71cfC_cont θ lam)
  have key : ∀ z₀ : ℂ, HasDerivAt
      (fun z : ℂ => ∫ t in (0:ℝ)..b, Complex.exp (-(z * (t:ℂ))) * tf71cfC θ lam t)
      (∫ t in (0:ℝ)..b, Complex.exp (-(z₀ * (t:ℂ))) * (-(t:ℂ)) * tf71cfC θ lam t) z₀ := by
    intro z₀
    set bound : ℝ → ℝ :=
      fun t => b * Real.exp ((‖z₀‖ + 1) * b) * ‖tf71cfC θ lam t‖ with hbound
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0:ℝ)) (b := b) (bound := bound)
      (F := fun z t => Complex.exp (-(z * (t:ℂ))) * tf71cfC θ lam t)
      (F' := fun z t => Complex.exp (-(z * (t:ℂ))) * (-(t:ℂ)) * tf71cfC θ lam t)
      (x₀ := z₀) (s := Metric.ball z₀ 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Metric.ball_mem_nhds z₀ one_pos
    · filter_upwards with x
      exact (hcontF x).aestronglyMeasurable
    · exact (hcontF z₀).intervalIntegrable 0 b
    · exact (hcontF' z₀).aestronglyMeasurable
    · filter_upwards with t ht x hx
      rw [Metric.mem_ball] at hx
      rw [Set.uIoc_of_le hbnonneg] at ht
      rw [hbound]
      have hxnorm : ‖x‖ ≤ ‖z₀‖ + 1 := by
        have h2 : ‖x - z₀‖ < 1 := by rwa [dist_eq_norm] at hx
        calc ‖x‖ = ‖(x - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖x - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ 1 + ‖z₀‖ := by linarith
          _ = ‖z₀‖ + 1 := by ring
      have ht_le : |t| ≤ b := by rw [abs_of_pos ht.1]; exact ht.2
      have h1 : ‖Complex.exp (-(x * (t:ℂ)))‖ ≤ Real.exp ((‖z₀‖ + 1) * b) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have hre : (-(x * (t:ℂ))).re = -(x.re * t) := by
          simp [Complex.neg_re, Complex.mul_re]
        rw [hre]
        calc -(x.re * t) ≤ |x.re * t| := neg_le_abs _
          _ = |x.re| * |t| := by rw [abs_mul]
          _ ≤ ‖x‖ * |t| :=
              mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm x) (abs_nonneg t)
          _ ≤ ‖x‖ * b := mul_le_mul_of_nonneg_left ht_le (norm_nonneg x)
          _ ≤ (‖z₀‖ + 1) * b := mul_le_mul_of_nonneg_right hxnorm hbnonneg
      have hab : ‖Complex.exp (-(x * (t:ℂ)))‖ * |t| ≤
          b * Real.exp ((‖z₀‖ + 1) * b) := by
        calc ‖Complex.exp (-(x * (t:ℂ)))‖ * |t|
            ≤ Real.exp ((‖z₀‖ + 1) * b) * |t| :=
              mul_le_mul_of_nonneg_right h1 (abs_nonneg t)
          _ ≤ Real.exp ((‖z₀‖ + 1) * b) * b :=
              mul_le_mul_of_nonneg_left ht_le (le_of_lt (Real.exp_pos _))
          _ = b * Real.exp ((‖z₀‖ + 1) * b) := by rw [mul_comm]
      have hneg : ‖(-(t:ℂ))‖ = |t| := by rw [norm_neg]; simp
      rw [norm_mul, norm_mul, hneg]
      exact mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    · rw [hbound]
      exact (continuous_const.mul ((tf71cfC_cont θ lam).norm)).intervalIntegrable 0 b
    · filter_upwards with t ht x hx
      have h0 : HasDerivAt (fun y : ℂ => y * (-(t:ℂ))) (-(t:ℂ)) x := by
        simpa using (hasDerivAt_id x).mul_const (-(t:ℂ))
      have hneg : HasDerivAt (fun y : ℂ => -(y * (t:ℂ))) (-(t:ℂ)) x :=
        h0.congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun y => (mul_neg y (t:ℂ)).symm))
      exact hneg.cexp.mul_const (tf71cfC θ lam t)
  intro z₀
  exact (key z₀).differentiableAt

end Work.ZeroFreeTables
