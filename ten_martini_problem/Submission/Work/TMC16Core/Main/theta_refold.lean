import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.theta_reduce

namespace Work.TMC16Core.Main

open Work.TMC16Core

/-- **Re-folding the index range.**  Suppose `fracDist (2θ + rα) ≥ c` for all integers `r`
with `|r| ≤ Q/2`, and let `Δ = fracDist (Qα)`.  If the "shift cost" `(Y/Q + 1/2) Δ` is at
most `c/2`, then the same lower bound, with `c` replaced by `c/2`, holds on the whole range
`|k| ≤ Y`.

Indeed, for `|k| ≤ Y` write `k = m Q + r` with `m = round (k/Q)` and `|r| ≤ Q/2`.  Then
`c ≤ fracDist (2θ + rα)`, while `2θ + rα` differs from `2θ + kα` by `m Q α`, whose
`fracDist` is at most `|m| Δ ≤ (Y/Q + 1/2) Δ ≤ c/2`. -/
theorem theta_refold {α θ : ℝ} {Q : ℕ} {Δ c Y : ℝ}
    (hQ : 0 < Q) (hc : 0 < c)
    (hΔ : Δ = Work.TMC16Core.fracDist ((Q : ℝ) * α))
    (hred : ∀ r : ℤ, |r| ≤ (Q : ℝ) / 2 → c ≤ Work.TMC16Core.fracDist (2 * θ + (r : ℝ) * α))
    (hshift : (Y / (Q : ℝ) + 1 / 2) * Δ ≤ c / 2) :
    ∀ k : ℤ, |(k : ℝ)| ≤ Y → c / 2 ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) := by
  intro k hk
  have hq : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hqne : (Q : ℝ) ≠ 0 := ne_of_gt hq
  set m : ℤ := round ((k : ℝ) / (Q : ℝ)) with hm
  set r : ℤ := k - m * (Q : ℤ) with hr
  -- `r` as a real number
  have hr_cast : (r : ℝ) = (k : ℝ) - (m : ℝ) * (Q : ℝ) := by
    rw [hr]; push_cast; ring
  have hr_mul : (r : ℝ) = (Q : ℝ) * ((k : ℝ) / (Q : ℝ) - (m : ℝ)) := by
    rw [hr_cast, mul_sub, mul_div_cancel₀ (k : ℝ) hqne]
    ring
  have hfd : fracDist ((k : ℝ) / (Q : ℝ)) = |(k : ℝ) / (Q : ℝ) - (m : ℝ)| := by
    rw [fracDist, ← hm]
  -- (A) `|r| ≤ Q/2`
  have hr_le : |(r : ℝ)| ≤ (Q : ℝ) / 2 := by
    have h : |(k : ℝ) / (Q : ℝ) - (m : ℝ)| ≤ 1 / 2 := by
      rw [← hfd]; exact Core.fracDist_le_half' _
    rw [hr_mul, abs_mul, abs_of_pos hq]
    nlinarith [h, hq]
  -- (B) `|m| ≤ |k|/Q + 1/2`
  have hm_le : |(m : ℝ)| ≤ |(k : ℝ)| / (Q : ℝ) + 1 / 2 := by
    have htri : |(m : ℝ)| ≤
        |(k : ℝ) / (Q : ℝ)| + |(k : ℝ) / (Q : ℝ) - (m : ℝ)| := by
      calc |(m : ℝ)| = |(k : ℝ) / (Q : ℝ) + ((m : ℝ) - (k : ℝ) / (Q : ℝ))| := by
            congr 1; ring
        _ ≤ |(k : ℝ) / (Q : ℝ)| + |(m : ℝ) - (k : ℝ) / (Q : ℝ)| := abs_add_le _ _
        _ = |(k : ℝ) / (Q : ℝ)| + |(k : ℝ) / (Q : ℝ) - (m : ℝ)| := by rw [abs_sub_comm]
    have hxa : |(k : ℝ) / (Q : ℝ)| = |(k : ℝ)| / (Q : ℝ) := by
      rw [abs_div, abs_of_pos hq]
    have hfdle : |(k : ℝ) / (Q : ℝ) - (m : ℝ)| ≤ 1 / 2 := by
      rw [← hfd]; exact Core.fracDist_le_half' _
    rw [hxa] at htri
    linarith [htri, hfdle]
  -- (C) `|m| ≤ Y/Q + 1/2`
  have hk_div : |(k : ℝ)| / (Q : ℝ) ≤ Y / (Q : ℝ) :=
    div_le_div_of_nonneg_right hk (le_of_lt hq)
  have hm_big : |(m : ℝ)| ≤ Y / (Q : ℝ) + 1 / 2 := by linarith [hm_le, hk_div]
  have hΔnn : 0 ≤ Δ := by rw [hΔ]; exact Core.fracDist_nonneg' _
  have hmΔ : |(m : ℝ)| * Δ ≤ c / 2 := by
    have h1 : |(m : ℝ)| * Δ ≤ (Y / (Q : ℝ) + 1 / 2) * Δ :=
      mul_le_mul_of_nonneg_right hm_big hΔnn
    linarith [h1, hshift]
  -- the reduced index satisfies the hypothesis of `hred`
  have hred_r : c ≤ fracDist (2 * θ + (r : ℝ) * α) := by
    refine hred r ?_
    rw [Int.cast_abs]
    exact hr_le
  have hb_le : fracDist ((m : ℝ) * ((Q : ℝ) * α)) ≤ |(m : ℝ)| * Δ := by
    calc fracDist ((m : ℝ) * ((Q : ℝ) * α))
        ≤ |(m : ℝ)| * fracDist ((Q : ℝ) * α) := Core.fracDist_zmul_le m ((Q : ℝ) * α)
      _ = |(m : ℝ)| * Δ := by rw [hΔ]
  have hkey : fracDist (2 * θ + (k : ℝ) * α)
      ≥ fracDist (2 * θ + (r : ℝ) * α) - |(m : ℝ)| * Δ := by
    have h := Core.le_fracDist_add' (2 * θ + (r : ℝ) * α) ((m : ℝ) * ((Q : ℝ) * α))
    have heq : 2 * θ + (r : ℝ) * α + (m : ℝ) * ((Q : ℝ) * α) = 2 * θ + (k : ℝ) * α := by
      rw [hr_cast]; ring
    rw [heq] at h
    linarith [h, hb_le]
  linarith [hkey, hred_r, hmΔ]

end Work.TMC16Core.Main
