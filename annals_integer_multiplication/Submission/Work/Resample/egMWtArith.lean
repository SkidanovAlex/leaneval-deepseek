import Mathlib
import Submission.Work.Resample.sliceB1defs

namespace Work.Resample

/-- For `n ≥ 4` we have `n² ≤ 2ⁿ`. -/
lemma sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k _hk ih =>
      have hstep : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
      calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := hstep
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

theorem egMWtArith (p α : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) :
    8 * (Work.Resample.egM p α : ℝ) + 5 ≤ (29 / 50) * (2 : ℝ) ^ p := by
  have hm : egM p α ≤ p + 1 := by
    have h := Nat.sqrt_le_self p
    have h2 := Nat.div_le_self (Nat.sqrt p) (2 * α)
    simp only [egM]
    omega
  have hmR : (egM p α : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hm
  have hpR : (100 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsq : (p : ℝ) ^ 2 ≤ (2 : ℝ) ^ p := by
    have h := sq_le_two_pow p (by omega)
    exact_mod_cast h
  have hA : 8 * (egM p α : ℝ) + 5 ≤ 8 * (p : ℝ) + 13 := by linarith
  have hB : 8 * (p : ℝ) + 13 ≤ (29 / 50) * (p : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (p : ℝ) - 100 := by linarith
    have h2 : (0 : ℝ) ≤ 29 * (p : ℝ) + 2500 := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hC : (29 / 50) * (p : ℝ) ^ 2 ≤ (29 / 50) * (2 : ℝ) ^ p :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  linarith

end Work.Resample
