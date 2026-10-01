import Mathlib
import Submission.Work.ZeroFreeTables.P9F.exp_series_bounds

namespace Work.ZeroFreeTables

open scoped BigOperators

/-- Upper Taylor bound for `Real.exp` on `[0,4]`: the degree-8 Taylor polynomial
plus twice the order-9 Lagrange-type remainder. -/
lemma tf72_exp_taylor_upper (t : ℝ) (ht0 : 0 ≤ t) (ht4 : t ≤ 4) :
    Real.exp t ≤ (∑ m ∈ Finset.range 9, t ^ m / (m.factorial : ℝ))
      + 2 * t ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ) := by
  have h9 : t < ((9 : ℕ) : ℝ) := by
    have : ((9 : ℕ) : ℝ) = 9 := by norm_num
    rw [this]; linarith
  obtain ⟨_, hub⟩ := P9F.exp_series_bounds 9 (by norm_num) t ht0 h9
  have hden : (0:ℝ) < 1 - t / 9 := by linarith
  have hfrac : (1:ℝ) / (1 - t / 9) ≤ 2 := by
    rw [div_le_iff₀ hden]; linarith
  have hpow : (0:ℝ) ≤ t ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ) :=
    div_nonneg (pow_nonneg ht0 9) (by positivity)
  calc Real.exp t
      ≤ (∑ m ∈ Finset.range 9, t ^ m / (m.factorial : ℝ))
          + t ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ) * (1 / (1 - t / 9)) := hub
    _ ≤ (∑ m ∈ Finset.range 9, t ^ m / (m.factorial : ℝ))
          + t ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ) * 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hfrac hpow)
    _ = (∑ m ∈ Finset.range 9, t ^ m / (m.factorial : ℝ))
          + 2 * t ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ) := by ring

end Work.ZeroFreeTables
