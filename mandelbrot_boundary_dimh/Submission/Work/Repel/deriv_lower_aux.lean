import Mathlib
import Submission.Work.Motion.koebe_distortion
import Submission.Work.Repel.bieberbach_two_aux
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Work.Repel.koebeT_iteratedDeriv_two
import Submission.Work.Repel.deriv_lower_of_second_deriv_bound

/-!
# Lower bound for the derivative of a holomorphic injection on a disc

For a holomorphic injection `f` on `closedBall c R` (injective on the open ball `ball c R`), the
derivative is bounded below by `‖deriv f c‖ / 12` on the half-ball `closedBall c (R / 2)`.

This is the classical weak lower half of Koebe's distortion theorem.  After rescaling we may
assume `c = 0`, `R = 1` and `deriv f 0 = 1`; then:

* the Koebe transform `k_z` of `f` at `z` (`Work.Motion.koebeT f z`) is again a normalised
  univalent function, so Bieberbach's inequality (`Work.Repel.bieberbach_two_aux`) applied to it
  gives `‖(1-‖z‖²) f''(z)/f'(z) - 2 conj z‖ ≤ 4`, i.e. `‖f''(z)/f'(z)‖ ≤ (4 + 2‖z‖)/(1 - ‖z‖²)`
  (`Work.Repel.koebeT_iteratedDeriv_two` is the second-coefficient computation);
* integrating that logarithmic-derivative bound along the segment from `0` to `z`
  (`Work.Repel.deriv_lower_of_second_deriv_bound`) gives `‖f'(z)‖ ≥ (1/12)‖f'(0)‖` for
  `‖z‖ ≤ 1/2`, since `∫₀^{1/2} (4+2s)/(1-s²) ds = log 12`.
-/

namespace Work.Repel

open Metric Set Filter
open scoped ComplexConjugate

/-- The unit-disc, normalised form of the distortion lower bound. -/
theorem deriv_lower_aux_unit {g : ℂ → ℂ}
    (han : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ g w)
    (hinj : Set.InjOn g (Metric.ball (0 : ℂ) 1)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (1 / 2), (1 / 12 : ℝ) * ‖deriv g 0‖ ≤ ‖deriv g z‖ := by
  have hbound : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      ‖deriv (deriv g) w‖ ≤ (4 + 2 * ‖w‖) / (1 - ‖w‖ ^ 2) * ‖deriv g w‖ := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hgw : deriv g w ≠ 0 := by
      refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
        (by linarith : (0 : ℝ) < 1 - ‖w‖) (han w hw) (hinj.mono ?_)
      intro a ha
      have ha' : ‖a - w‖ < 1 - ‖w‖ := by simpa [Metric.mem_ball, dist_eq_norm] using ha
      have h1 : ‖a‖ ≤ ‖a - w‖ + ‖w‖ := by
        calc ‖a‖ = ‖(a - w) + w‖ := by ring_nf
          _ ≤ ‖a - w‖ + ‖w‖ := norm_add_le _ _
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
      linarith
    obtain ⟨hkan, hkinj, hk0, hk1⟩ := Work.Motion.koebeT_normalized han hinj hw hgw
    have hB : ‖iteratedDeriv 2 (Work.Motion.koebeT g w) 0‖ ≤ 4 :=
      bieberbach_two_aux hkan hkinj hk0 hk1
    have hform : iteratedDeriv 2 (Work.Motion.koebeT g w) 0
        = (1 - ‖w‖ ^ 2) * deriv (deriv g) w / deriv g w - 2 * conj w :=
      koebeT_iteratedDeriv_two hw han hgw
    rw [hform] at hB
    have hstep : ‖(1 - (‖w‖ : ℂ) ^ 2) * deriv (deriv g) w / deriv g w‖ ≤ 4 + 2 * ‖w‖ := by
      have h2 : ‖(2 : ℂ) * conj w‖ = 2 * ‖w‖ := by
        rw [norm_mul, Complex.norm_conj]; norm_num
      calc ‖(1 - (‖w‖ : ℂ) ^ 2) * deriv (deriv g) w / deriv g w‖
          = ‖((1 - (‖w‖ : ℂ) ^ 2) * deriv (deriv g) w / deriv g w - 2 * conj w) + 2 * conj w‖ := by
            congr 1; ring
        _ ≤ ‖(1 - (‖w‖ : ℂ) ^ 2) * deriv (deriv g) w / deriv g w - 2 * conj w‖ + ‖2 * conj w‖ :=
            norm_add_le _ _
        _ ≤ 4 + 2 * ‖w‖ := by rw [h2]; linarith
    have hgn : 0 < ‖deriv g w‖ := norm_pos_iff.mpr hgw
    have hnorm : ‖((1 - ‖w‖ ^ 2 : ℝ) : ℂ)‖ = 1 - ‖w‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hc : ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) = 1 - (‖w‖ : ℂ) ^ 2 := by push_cast; ring
    have h1 : (1 - ‖w‖ ^ 2) * ‖deriv (deriv g) w‖ ≤ (4 + 2 * ‖w‖) * ‖deriv g w‖ := by
      rw [← hc, norm_div, norm_mul, hnorm] at hstep
      rw [div_le_iff₀ hgn] at hstep
      exact hstep
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    rw [mul_comm (‖deriv (deriv g) w‖) (1 - ‖w‖ ^ 2)]
    exact h1
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
  exact deriv_lower_of_second_deriv_bound han hbound hz

theorem deriv_lower_aux {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hinj : Set.InjOn f (Metric.ball c R)) :
    ∀ z ∈ Metric.closedBall c (R / 2), (1 / 12 : ℝ) * ‖deriv f c‖ ≤ ‖deriv f z‖ := by
  intro z hz
  rcases eq_or_ne (deriv f c) 0 with hDc | hDc
  · rw [hDc, norm_zero, mul_zero]; exact norm_nonneg _
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hDne : (R : ℂ) * deriv f c ≠ 0 := mul_ne_zero hRne hDc
  set g : ℂ → ℂ := fun w => (f (c + (R : ℂ) * w) - f c) / ((R : ℂ) * deriv f c) with hgdef
  have hmem : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 → c + (R : ℂ) * w ∈ Metric.ball c R := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show c + (R : ℂ) * w - c = (R : ℂ) * w by ring, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    nlinarith
  have hgan : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ g w := by
    intro w hw
    rw [hgdef]
    have hwm : c + (R : ℂ) * w ∈ Metric.ball c R := hmem w hw
    have hf_at : AnalyticAt ℂ f (c + (R : ℂ) * w) :=
      hf.analyticAt (mem_of_superset (Metric.isOpen_ball.mem_nhds hwm) Metric.ball_subset_closedBall)
    have hinner : AnalyticAt ℂ (fun v : ℂ => c + (R : ℂ) * v) w :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    have h1 : AnalyticAt ℂ (fun v : ℂ => f (c + (R : ℂ) * v)) w :=
      AnalyticAt.comp hf_at hinner
    have h2 : AnalyticAt ℂ (fun v : ℂ => f (c + (R : ℂ) * v) - f c) w := h1.sub analyticAt_const
    exact h2.div_const (c := (R : ℂ) * deriv f c)
  have hginj : Set.InjOn g (Metric.ball (0 : ℂ) 1) := by
    intro w1 hw1 w2 hw2 heq
    rw [hgdef] at heq
    have h1 : f (c + (R : ℂ) * w1) - f c = f (c + (R : ℂ) * w2) - f c :=
      (div_left_inj' hDne).mp heq
    have h2 : f (c + (R : ℂ) * w1) = f (c + (R : ℂ) * w2) := by
      have := congrArg (fun y => y + f c) h1; simpa using this
    have h3 : c + (R : ℂ) * w1 = c + (R : ℂ) * w2 :=
      hinj (hmem w1 hw1) (hmem w2 hw2) h2
    have h4 : (R : ℂ) * w1 = (R : ℂ) * w2 := add_left_cancel h3
    exact mul_left_cancel₀ hRne h4
  have hg0 : g 0 = 0 := by rw [hgdef]; simp
  have hdc : DifferentiableAt ℂ f c := by
    apply hf.differentiableAt
    exact mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)) Metric.ball_subset_closedBall
  have hdaff : ∀ v : ℂ, DifferentiableAt ℂ f (c + (R : ℂ) * v) →
      deriv (fun w : ℂ => f (c + (R : ℂ) * w)) v = deriv f (c + (R : ℂ) * v) * (R : ℂ) := by
    intro v hv
    have h1 : HasDerivAt (fun w : ℂ => c + (R : ℂ) * w) (R : ℂ) v := by
      simpa using ((hasDerivAt_id v).const_mul (R : ℂ)).const_add c
    have h2 : HasDerivAt (fun w : ℂ => f (c + (R : ℂ) * w)) (deriv f (c + (R : ℂ) * v) * (R : ℂ)) v := by
      simpa [Function.comp_def] using (hv.hasDerivAt.comp v h1)
    exact h2.deriv
  have hg1 : deriv g 0 = 1 := by
    rw [hgdef, deriv_div_const, deriv_sub_const, hdaff 0 (by rw [mul_zero, add_zero]; exact hdc),
      show c + (R : ℂ) * 0 = c by ring, mul_comm (deriv f c) (R : ℂ), div_self hDne]
  have hunit := deriv_lower_aux_unit hgan hginj
  set w : ℂ := (z - c) / (R : ℂ) with hwdef
  have hzw : c + (R : ℂ) * w = z := by
    rw [hwdef]; field_simp; ring
  have hzc : ‖z - c‖ ≤ R / 2 := by
    have hh := mem_closedBall.mp hz
    rwa [dist_eq_norm] at hh
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hwdef, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
    linarith
  have h := hunit w hwmem
  rw [hg1, norm_one, mul_one] at h
  have hzR : z ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hderiv : deriv g w = deriv f z / deriv f c := by
    have hd : DifferentiableAt ℂ f (c + (R : ℂ) * w) := by
      rw [hzw]
      exact hf.differentiableAt (mem_of_superset (Metric.isOpen_ball.mem_nhds hzR) Metric.ball_subset_closedBall)
    rw [hgdef, deriv_div_const, deriv_sub_const, hdaff w hd, hzw]
    rw [mul_comm (deriv f z) (R : ℂ), mul_div_mul_left _ _ hRne]
  rw [hderiv, norm_div] at h
  rw [le_div_iff₀ (norm_pos_iff.mpr hDc)] at h
  linarith

end Work.Repel
