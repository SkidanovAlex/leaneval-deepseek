import Mathlib
import Submission.Work.Motion.pertSupport

namespace Work.Motion

open Set Metric in
/-- In the setting of `newtonFixpoint`, the solution `v` of `F v = -A` in `closedBall 0 ε`
actually lies in the *open* ball: the Newton map maps `closedBall 0 ε` into `closedBall 0 (ε/2)`,
and `v` is a fixed point of it. -/
theorem norm_newtonFixpoint_lt {F : ℂ → ℂ} {A B : ℂ} {ε b : ℝ}
    (hb : 0 < b) (hε : 0 < ε) (hF0 : F 0 = 0) (hB : b ≤ ‖B‖) (hA : ‖A‖ ≤ b * ε / 4)
    (hd : ∀ w ∈ closedBall (0 : ℂ) ε, DifferentiableAt ℂ F w)
    (hbd : ∀ w ∈ closedBall (0 : ℂ) ε, ‖deriv F w - B‖ ≤ b / 4)
    {v : ℂ} (hv : F v = -A) (hvm : v ∈ closedBall (0 : ℂ) ε) :
    ‖v‖ < ε := by
  have hBpos : 0 < ‖B‖ := lt_of_lt_of_le hb hB
  have hBne : B ≠ 0 := norm_pos_iff.mp hBpos
  -- The MVT bound for the linearised remainder `H w = F w - B w`, from the base point `0`.
  have hrem := Pert.newton_remainder_bound (F := F) (B := B) (ε := ε) (b := b)
    hd hbd hvm (mem_closedBall_self hε.le)
  have hH0 : F 0 - B * 0 = 0 := by rw [hF0, mul_zero, sub_zero]
  rw [hH0, sub_zero, sub_zero] at hrem
  have hvm' : ‖v‖ ≤ ε := by
    have h := hvm; rw [mem_closedBall, dist_eq_norm] at h; simpa using h
  have hA' : ‖A‖ ≤ b / 4 * ε := by
    rw [show b * ε / 4 = b / 4 * ε by ring] at hA; exact hA
  -- `v` is a fixed point of the Newton map `w ↦ w - (A + F w)/B`.
  have hvfix : v - (A + F v) / B = v := by rw [hv]; ring
  -- hence `‖v‖ = ‖(H v + A)/B‖`
  have heq : v = -((F v - B * v) + A) / B :=
    hvfix.symm.trans (by field_simp; ring)
  have hnum : ‖(F v - B * v) + A‖ ≤ b * ε / 2 := by
    calc ‖(F v - B * v) + A‖ ≤ ‖F v - B * v‖ + ‖A‖ := norm_add_le _ _
      _ ≤ b / 4 * ‖v‖ + b / 4 * ε := add_le_add hrem hA'
      _ ≤ b / 4 * ε + b / 4 * ε := by gcongr
      _ = b * ε / 2 := by ring
  rw [heq, norm_div, norm_neg]
  have h2 : ‖(F v - B * v) + A‖ / ‖B‖ ≤ (b * ε / 2) / b :=
    div_le_div₀ (by positivity) hnum hb hB
  have h3 : (b * ε / 2) / b = ε / 2 := by field_simp
  linarith

end Work.Motion
