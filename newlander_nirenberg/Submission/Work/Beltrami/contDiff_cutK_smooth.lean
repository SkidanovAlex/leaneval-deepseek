import Mathlib
import Submission.Work.Beltrami.dbarW_cauchyT_defs

namespace Work.Beltrami

open Filter

/-- The cutoff kernel `cutK ε` vanishes identically in a neighbourhood of the origin:
for `‖u‖ < |ε|` the profile `ψ(‖u‖²/ε² - 1)` is `0`, and for `ε = 0` it is `0` everywhere. -/
theorem cutK_eventuallyEq_zero (ε : ℝ) :
    cutK ε =ᶠ[nhds (0 : ℂ)] (fun _ => (0 : ℂ)) := by
  rcases eq_or_ne ε 0 with h | h
  · subst h
    filter_upwards with u
    simp [cutK, cutProfile, Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
  · rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Metric.ball (0 : ℂ) |ε|, Metric.ball_mem_nhds 0 (abs_pos.mpr h), ?_⟩
    intro u hu
    rw [Metric.mem_ball, dist_zero_right] at hu
    have hε2 : 0 < ε ^ 2 := sq_pos_of_ne_zero h
    have hsq : (|ε| : ℝ) ^ 2 = ε ^ 2 := sq_abs ε
    have hlt : ‖u‖ ^ 2 < ε ^ 2 := by nlinarith [norm_nonneg u, abs_nonneg ε]
    have h3 : ‖u‖ ^ 2 / ε ^ 2 < 1 := (div_lt_one hε2).mpr hlt
    have h4 : ‖u‖ ^ 2 / ε ^ 2 - 1 < 0 := by linarith
    simp [cutK, cutProfile, Real.smoothTransition.zero_of_nonpos (le_of_lt h4)]

/-- The cutoff profile `s ↦ ψ(s/ε² - 1)` is smooth of every finite order. -/
theorem cutProfile_contDiff (ε : ℝ) (n : ℕ∞) :
    ContDiff ℝ (n : WithTop ℕ∞) (cutProfile ε) := by
  have h := Real.smoothTransition.contDiff (n := n)
  unfold cutProfile
  exact h.comp (by fun_prop)

/-- The radial cutoff `u ↦ ψ(‖u‖²/ε² - 1)`, viewed as a complex-valued function, is smooth
of every finite order. -/
theorem radialCut_contDiff (ε : ℝ) (n : ℕ∞) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun u : ℂ => (cutProfile ε (‖u‖ ^ 2) : ℂ)) := by
  have hbase : ContDiff ℝ (n : WithTop ℕ∞) (fun u : ℂ => cutProfile ε (‖u‖ ^ 2)) :=
    (cutProfile_contDiff ε n).comp (contDiff_norm_sq ℝ (n := (n : WithTop ℕ∞)))
  exact (ContinuousLinearMap.contDiff Complex.ofRealCLM :
    ContDiff ℝ (n : WithTop ℕ∞) ⇑Complex.ofRealCLM).comp hbase

/-- The cutoff kernel `ψ(‖u‖²/ε² - 1) · u⁻¹` is `C¹`: away from the origin it is the product
of a smooth radial factor and the smooth map `u ↦ u⁻¹`, and near the origin it vanishes
identically. -/
theorem contDiff_cutK_smooth (ε : ℝ) : ContDiff ℝ 1 (cutK ε) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (cutK_eventuallyEq_zero ε)
  · have h1 : ContDiffAt ℝ 1 (fun u : ℂ => (cutProfile ε (‖u‖ ^ 2) : ℂ)) u :=
      (radialCut_contDiff ε 1).contDiffAt
    have h2 : ContDiffAt ℝ 1 (fun z : ℂ => z⁻¹) u :=
      ContDiffAt.inv (f := fun z : ℂ => z) contDiffAt_id hu
    change ContDiffAt ℝ 1 (fun x : ℂ => (cutProfile ε (‖x‖ ^ 2) : ℂ) * x⁻¹) u
    exact h1.mul h2

end Work.Beltrami
