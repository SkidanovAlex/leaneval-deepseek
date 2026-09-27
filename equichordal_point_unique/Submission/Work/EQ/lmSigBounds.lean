import Mathlib
import Submission.Work.EQ.LocModelDefs

set_option linter.unusedVariables false

namespace Work.EQ

/-- In the local model we always have `a < lmS a a₀ < 1`, and the box half-width
`lmH a a₀` is at most `lmS a a₀ / 16`.  Consequently, for `|ξ|, |η| ≤ lmH a a₀` the
radius `σ = lmSig a a₀ ξ η` stays inside `[lmS/2, 2*lmS]`, which controls the first
multiplier `lmG₁ = 1 - 1/σ` and the first image `lmY₁ = η * lmG₁`. -/
theorem lmSigBounds {a a₀ ξ η : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ Work.EQ.lmH a a₀) (hη : |η| ≤ Work.EQ.lmH a a₀) :
    Work.EQ.lmS a a₀ / 2 ≤ Work.EQ.lmSig a a₀ ξ η ∧ Work.EQ.lmSig a a₀ ξ η ≤ 2 * Work.EQ.lmS a a₀ ∧
    |Work.EQ.lmG1 a a₀ ξ η| ≤ 1 + 2/Work.EQ.lmS a a₀ ∧ |Work.EQ.lmY1 a a₀ ξ η| ≤ 3/16 := by
  have hs : 0 < lmS a a₀ := by rw [lmS]; linarith
  have hs1 : lmS a a₀ < 1 := by rw [lmS]; linarith
  -- The half-width of the box is bounded by `lmS / 16`.
  have hHle : lmH a a₀ ≤ lmS a a₀ / 16 := by
    rw [lmH]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hxi : |ξ| ≤ lmS a a₀ / 16 := le_trans hξ hHle
  have heta : |η| ≤ lmS a a₀ / 16 := le_trans hη hHle
  have hξle : ξ ≤ lmS a a₀ / 16 := (abs_le.mp hxi).2
  have hξge : -(lmS a a₀ / 16) ≤ ξ := (abs_le.mp hxi).1
  have hηle : η ≤ lmS a a₀ / 16 := (abs_le.mp heta).2
  have hηge : -(lmS a a₀ / 16) ≤ η := (abs_le.mp heta).1
  -- Lower bound: `σ ≥ s/2`, since `u = ξ - s ≤ -15s/16 < 0` and `|u| ≥ s/2`.
  have hlo : lmS a a₀ / 2 ≤ lmSig a a₀ ξ η := by
    rw [lmSig, lmU_eq]
    exact (Real.le_sqrt (by linarith) (by positivity)).mpr (by
      have hp : (lmS a a₀ / 2 - (ξ - lmS a a₀)) * (lmS a a₀ / 2 + (ξ - lmS a a₀)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      nlinarith [hp, sq_nonneg η])
  -- Upper bound: `σ ≤ 2s`, since `u² ≤ (17s/16)²` and `η² ≤ (s/16)²`.
  have hhi : lmSig a a₀ ξ η ≤ 2 * lmS a a₀ := by
    rw [lmSig, lmU_eq]
    refine (Real.sqrt_le_left (show 0 ≤ 2 * lmS a a₀ by linarith)).mpr ?_
    have hu : |ξ - lmS a a₀| ≤ 17 * lmS a a₀ / 16 := by
      rw [abs_le]; constructor <;> linarith
    have hsq1 : (ξ - lmS a a₀)^2 ≤ (17 * lmS a a₀ / 16)^2 := by
      have habs : |17 * lmS a a₀ / 16| = 17 * lmS a a₀ / 16 := abs_of_nonneg (by linarith)
      rw [sq_le_sq, habs]; exact hu
    have hsq2 : η^2 ≤ (lmS a a₀ / 16)^2 := by
      have habs : |lmS a a₀ / 16| = lmS a a₀ / 16 := abs_of_nonneg (by linarith)
      rw [sq_le_sq, habs]; exact heta
    nlinarith [hsq1, hsq2, sq_nonneg (lmS a a₀)]
  have hσpos : 0 < lmSig a a₀ ξ η := lt_of_lt_of_le (by linarith) hlo
  have hinv : 1 / lmSig a a₀ ξ η ≤ 2 / lmS a a₀ := by
    have h := one_div_le_one_div_of_le (show 0 < lmS a a₀ / 2 by linarith) hlo
    rwa [one_div_div] at h
  -- Bound on `lmG₁ = 1 - 1/σ`: `|1 - 1/σ| ≤ 1 + 1/σ ≤ 1 + 2/s`.
  have hg1 : |lmG1 a a₀ ξ η| ≤ 1 + 2/lmS a a₀ := by
    rw [lmG1, inv_eq_one_div]
    have hσinv_nonneg : 0 ≤ 1 / lmSig a a₀ ξ η := div_nonneg zero_le_one (le_of_lt hσpos)
    calc |1 - 1 / lmSig a a₀ ξ η| ≤ 1 + 1 / lmSig a a₀ ξ η := by
          rw [abs_le]; constructor <;> linarith
      _ ≤ 1 + 2 / lmS a a₀ := by linarith
  -- Bound on `lmY₁ = η * lmG₁`: `≤ (s/16) * (1 + 2/s) = (s+2)/16 < 3/16`.
  have hy1 : |lmY1 a a₀ ξ η| ≤ 3/16 := by
    rw [lmY1_eq, abs_mul]
    have hb : |η| * |lmG1 a a₀ ξ η| ≤ (lmS a a₀ / 16) * (1 + 2/lmS a a₀) :=
      mul_le_mul heta hg1 (abs_nonneg _) (by linarith)
    have hsimp : (lmS a a₀ / 16) * (1 + 2/lmS a a₀) = (lmS a a₀ + 2)/16 := by
      have hne : lmS a a₀ ≠ 0 := ne_of_gt hs
      field_simp
    rw [hsimp] at hb
    linarith
  exact ⟨hlo, hhi, hg1, hy1⟩

end Work.EQ
