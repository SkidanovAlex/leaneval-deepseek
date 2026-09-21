import Mathlib
import Submission.Work.OddCurve.Defs
import Submission.Work.OddCurve.ball_moment_identity

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set
open scoped Interval

lemma rad_zero_semicircle {s t : ℝ}
    (ht : t ∈ Set.Icc (-(1 / Real.sqrt (1 + s ^ 2))) (1 / Real.sqrt (1 + s ^ 2))) :
    rad (fun _ : ℝ => 0) Work.OddEnvelope.semicircle s t = 1 - t ^ 2 - (s * t) ^ 2 := by
  have hle : 1 / Real.sqrt (1 + s ^ 2) ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 1 + s ^ 2))]
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg s])
  have ht1 : t ≤ (1 : ℝ) := le_trans ht.2 hle
  have ht2 : (-1 : ℝ) ≤ t := by linarith [ht.1, hle]
  have hsq : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith : (0 : ℝ) ≤ 1 + t)]
  have hsemi : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
    rw [Work.OddEnvelope.semicircle, Real.sq_sqrt hsq]
  simp only [rad, hsemi]
  ring

lemma momentA_zero_semicircle (n : ℕ) (s : ℝ) :
    momentA n (fun _ : ℝ => 0) Work.OddEnvelope.profileX Work.OddEnvelope.profileX
        Work.OddEnvelope.semicircle s = refConst n / Real.sqrt (1 + s ^ 2) := by
  rw [momentA_def]
  simp only [Work.OddEnvelope.profileX]
  have hcongr :
      (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        rad (fun _ : ℝ => 0) Work.OddEnvelope.semicircle s t ^ n *
          Real.sqrt (rad (fun _ : ℝ => 0) Work.OddEnvelope.semicircle s t)) =
      ∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (show -(1 / Real.sqrt (1 + s ^ 2)) ≤ 1 / Real.sqrt (1 + s ^ 2) by
      have h : (0 : ℝ) ≤ 1 / Real.sqrt (1 + s ^ 2) := by positivity
      linarith)] at ht
    dsimp only
    rw [rad_zero_semicircle ht]
  rw [hcongr]
  exact (ball_moment_identity n s).1

lemma momentB_zero_semicircle (n : ℕ) (s : ℝ) :
    momentB n (fun _ : ℝ => 0) Work.OddEnvelope.profileX Work.OddEnvelope.profileX
        Work.OddEnvelope.semicircle s = 0 := by
  rw [momentB_def]
  simp only [Work.OddEnvelope.profileX]
  have hderiv : deriv (fun _ : ℝ => (0 : ℝ)) s = 0 := deriv_const s 0
  have hcongr :
      (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        rad (fun _ : ℝ => 0) Work.OddEnvelope.semicircle s t ^ (n - 1) *
          Real.sqrt (rad (fun _ : ℝ => 0) Work.OddEnvelope.semicircle s t) *
          (t + deriv (fun _ : ℝ => 0) s)) =
      ∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (show -(1 / Real.sqrt (1 + s ^ 2)) ≤ 1 / Real.sqrt (1 + s ^ 2) by
      have h : (0 : ℝ) ≤ 1 / Real.sqrt (1 + s ^ 2) := by positivity
      linarith)] at ht
    dsimp only
    rw [rad_zero_semicircle ht, hderiv]
    ring
  rw [hcongr]
  exact (ball_moment_identity n s).2

theorem semicircle_moment_eqs (n : ℕ) :
    Work.OddCurve.MomentEqsOn n (Work.OddCurve.refConst n) (fun _ : ℝ => 0)
      Work.OddEnvelope.profileX Work.OddEnvelope.profileX Work.OddEnvelope.semicircle
      (Set.Ioi 0) := by
  constructor
  · intro s _
    exact momentA_zero_semicircle n s
  · intro s _
    exact momentB_zero_semicircle n s

end

end Work.OddCurve
