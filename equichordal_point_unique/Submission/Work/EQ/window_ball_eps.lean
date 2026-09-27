import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

/-- Multiplication by the nonzero constant `(eqLam a)^M` maps a small ball around any point
whose image lies inside `ball 0 ρ` into `ball 0 ρ`.  The radius is chosen explicitly so that
it is also at most `1/2`. -/
theorem window_ball_eps {a : ℝ} {M : ℕ} {p2 : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hlam : eqLam a ≠ 0) (hball : (eqLam a : ℂ) ^ M * p2 ∈ Metric.ball (0 : ℂ) ρ) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε ≤ 1 ∧
      ∀ z : ℂ, ‖z - p2‖ < ε → (eqLam a : ℂ) ^ M * z ∈ Metric.ball (0 : ℂ) ρ := by
  have hlamC : (eqLam a : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hcne : (eqLam a : ℂ) ^ M ≠ 0 := pow_ne_zero M hlamC
  have hcpos : 0 < ‖(eqLam a : ℂ) ^ M‖ := norm_pos_iff.mpr hcne
  have hρpos : 0 < ρ := hρ
  have hb : ‖(eqLam a : ℂ) ^ M * p2‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hball
  have hnum : 0 < ρ - ‖(eqLam a : ℂ) ^ M * p2‖ := by linarith
  refine ⟨min (1 / 2) ((ρ - ‖(eqLam a : ℂ) ^ M * p2‖) / (2 * ‖(eqLam a : ℂ) ^ M‖)),
    lt_min (by norm_num) (div_pos hnum (by positivity)), ?_, ?_⟩
  · have h1 := min_le_left (1 / 2)
      ((ρ - ‖(eqLam a : ℂ) ^ M * p2‖) / (2 * ‖(eqLam a : ℂ) ^ M‖))
    linarith
  · intro z hz
    have hzle : ‖z - p2‖ ≤ (ρ - ‖(eqLam a : ℂ) ^ M * p2‖) / (2 * ‖(eqLam a : ℂ) ^ M‖) :=
      le_trans (le_of_lt hz)
        (min_le_right (1 / 2) ((ρ - ‖(eqLam a : ℂ) ^ M * p2‖) / (2 * ‖(eqLam a : ℂ) ^ M‖)))
    have hsplit : (eqLam a : ℂ) ^ M * z =
        (eqLam a : ℂ) ^ M * (z - p2) + (eqLam a : ℂ) ^ M * p2 := by ring
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hsplit]
    calc ‖(eqLam a : ℂ) ^ M * (z - p2) + (eqLam a : ℂ) ^ M * p2‖
        ≤ ‖(eqLam a : ℂ) ^ M * (z - p2)‖ + ‖(eqLam a : ℂ) ^ M * p2‖ := norm_add_le _ _
      _ = ‖(eqLam a : ℂ) ^ M‖ * ‖z - p2‖ + ‖(eqLam a : ℂ) ^ M * p2‖ := by rw [norm_mul]
      _ ≤ ‖(eqLam a : ℂ) ^ M‖ *
            ((ρ - ‖(eqLam a : ℂ) ^ M * p2‖) / (2 * ‖(eqLam a : ℂ) ^ M‖)) +
            ‖(eqLam a : ℂ) ^ M * p2‖ := by
            gcongr
      _ < ρ := by
            have h : ‖(eqLam a : ℂ) ^ M‖ *
                ((ρ - ‖(eqLam a : ℂ) ^ M * p2‖) / (2 * ‖(eqLam a : ℂ) ^ M‖)) =
                (ρ - ‖(eqLam a : ℂ) ^ M * p2‖) / 2 := by
              field_simp
            rw [h]
            linarith

end Work.EQ
