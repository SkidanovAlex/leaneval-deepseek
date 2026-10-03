import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Parab.inversion.exists_mul_log_lt

/-!
# `Work.Pert.Ksub2.Xc_sub_id_le`

The datum's curve `u ↦ Xc d u = τ₀ (φ₀ u)` is within `M/40` of the identity on the whole deep
disc `closedBall (-M) (M/10)`, for all large `M`.

This is the *global* form of the deviation estimate of `Work.Pert.Ksub2.Xcurve_bounds`: for
`u` in that disc one has `9M/10 ≤ ‖u‖ ≤ 11M/10` and `Re u ≤ -9M/10`, and the disc
`ball u (‖u‖/10)` used by Cauchy's estimate lies in the half plane `{Re w < -ξ₀} ⊆ QLeft ξ₀`.
Hence `Xcurve_bounds` gives `‖Xc d u - u‖ ≤ C (1 + log ‖u‖) ≤ C (1 + log (2M))`, and
`log = o(id)` (`exists_mul_log_lt_aux`) makes this smaller than `M/40`.
-/

namespace Work.Pert.Ksub2

open Complex Metric

theorem Xc_sub_id_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℝ, R ≤ M →
      ∀ u ∈ Metric.closedBall (((-M : ℝ) : ℂ)) (M / 10),
        ‖Work.Pert.Xc d u - u‖ ≤ M / 40 := by
  obtain ⟨C, hCpos, hC⟩ := Xcurve_bounds d
  obtain ⟨R₀, _hR₀pos, hR₀⟩ :=
    Work.Parab.inversion.exists_mul_log_lt_aux (a := C) (b := C) (c := 1 / 40) (by norm_num)
  refine ⟨max (max (20 * d.ξ₀ + 20) (10 * C / 9 + 1)) (max R₀ 1), ?_, ?_⟩
  · exact lt_max_iff.mpr (Or.inl (lt_max_iff.mpr (Or.inl (by linarith [d.ξ₀_pos]))))
  · intro M hM u hu
    have hM_A : 20 * d.ξ₀ + 20 ≤ M :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
    have hM_B : 10 * C / 9 + 1 ≤ M :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
    have hM_R0 : R₀ ≤ M :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
    have hM_1 : (1 : ℝ) ≤ M :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
    have hMpos : 0 < M := lt_of_lt_of_le one_pos hM_1
    -- ## position and norm of `u`
    have hdist : ‖u - (((-M : ℝ) : ℂ))‖ ≤ M / 10 := by
      have := Metric.mem_closedBall.mp hu
      rwa [dist_eq_norm] at this
    have hadd : u - (((-M : ℝ) : ℂ)) = u + (M : ℂ) := by push_cast; ring
    have hdist' : ‖u + (M : ℂ)‖ ≤ M / 10 := by rw [← hadd]; exact hdist
    have hnormM : ‖(M : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hMpos.le]
    have hre : u.re ≤ -(9 * M / 10) := by
      have h1 : |(u + (M : ℂ)).re| ≤ ‖u + (M : ℂ)‖ := Complex.abs_re_le_norm _
      have h2 : (u + (M : ℂ)).re = u.re + M := by simp
      rw [h2] at h1
      have h3 := le_trans (le_abs_self (u.re + M)) h1
      linarith
    have hnorm_lo : 9 * M / 10 ≤ ‖u‖ := by
      have h1 : (M : ℝ) ≤ ‖u + (M : ℂ)‖ + ‖u‖ := by
        have h := norm_sub_le (u + (M : ℂ)) u
        have h2 : u + (M : ℂ) - u = (M : ℂ) := by ring
        rw [h2, hnormM] at h
        exact h
      linarith
    have hnorm_hi : ‖u‖ ≤ 11 * M / 10 := by
      have h1 : ‖u‖ ≤ ‖u + (M : ℂ)‖ + M := by
        have h := norm_add_le (u + (M : ℂ)) (-(M : ℂ))
        have h2 : u + (M : ℂ) + -(M : ℂ) = u := by ring
        rw [h2, norm_neg, hnormM] at h
        exact h
      linarith
    -- ## sector membership of `u` and of the disc `ball u (‖u‖/10)`
    have hgoal_u : u.re < -d.ξ₀ := by linarith
    have huQ : u ∈ MandelDim.QLeft d.ξ₀ := Work.Parab.halfplane_subset_QLeft d.ξ₀ hgoal_u
    have hball : Metric.ball u (‖u‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ := by
      intro v hv
      have hgoal_v : v.re < -d.ξ₀ := by
        have hv1 : ‖v - u‖ < ‖u‖ / 10 := by
          have := Metric.mem_ball.mp hv
          rwa [dist_eq_norm] at this
        have hv2 : ‖v - u‖ < 11 * M / 100 := by linarith
        have hvre : v.re ≤ u.re + ‖v - u‖ := by
          have h1 : (v - u).re = v.re - u.re := Complex.sub_re v u
          have h2 : (v - u).re ≤ ‖v - u‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
          linarith
        linarith
      exact Work.Parab.halfplane_subset_QLeft d.ξ₀ hgoal_v
    have hCu : C ≤ ‖u‖ := by linarith
    -- ## the value estimate
    have hb := (hC u huQ hCu hball).1
    have hlogu : Real.log ‖u‖ ≤ Real.log (2 * M) := by
      have h1 : (0 : ℝ) < ‖u‖ := by linarith
      have h2 : ‖u‖ ≤ 2 * M := by linarith
      exact Real.log_le_log h1 h2
    have hlog_le : C * (1 + Real.log ‖u‖) ≤ C * (1 + Real.log (2 * M)) := by
      have h := mul_le_mul_of_nonneg_left hlogu hCpos.le
      linarith
    have hR0M := hR₀ M hM_R0
    have hkey : C * (1 + Real.log (2 * M)) < M / 40 := by
      have he : C * (1 + Real.log (2 * M)) = C + C * Real.log (2 * M) := by ring
      rw [he]; linarith
    exact le_trans hb (le_trans hlog_le hkey.le)

end Work.Pert.Ksub2
