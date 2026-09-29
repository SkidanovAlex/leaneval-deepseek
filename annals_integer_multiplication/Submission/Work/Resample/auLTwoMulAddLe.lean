import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auMLe

namespace Work.Resample

/-- For `n ≥ 100`, `2 ^ n` dominates the linear expression `32 n + 16` (the exact form needed
to bound `2 · auL p α + 2`: `auL p α ≤ 4 p + 1` gives `2 · auL p α + 2 ≤ 8 p + 4 = (32 p + 16)/4`). -/
theorem auPowTwoGeLinearNat (n : ℕ) (hn : 100 ≤ n) : 32 * n + 16 ≤ 2 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 100 + m := ⟨n - 100, by omega⟩
  clear hn
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h3 : 2 * 2 ^ (100 + m) = 2 ^ (100 + (m + 1)) := by
      rw [show 100 + (m+1) = (100+m) + 1 from by omega, pow_succ]; ring
    calc 32 * (100 + (m + 1)) + 16 ≤ 2 * (32 * (100 + m) + 16) := by omega
      _ ≤ 2 * 2 ^ (100 + m) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (100 + (m + 1)) := h3

/-- Real form of `auPowTwoGeLinearNat`. -/
theorem auPowTwoGeLinear (n : ℕ) (hn : 100 ≤ n) : (32:ℝ) * (n:ℝ) + 16 ≤ (2:ℝ)^n := by
  have hn' := auPowTwoGeLinearNat n hn
  calc (32:ℝ) * (n:ℝ) + 16 = ((32 * n + 16 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hn'
    _ = (2:ℝ)^n := by push_cast; ring

theorem auLTwoMulAddLe (p α : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) (hαp : α ^ 2 < p) :
    (2 : ℝ) * (Work.Resample.auL p α : ℝ) + 2 ≤ (2 : ℝ) ^ p / 4 := by
  have hL : auL p α ≤ 4 * p + 1 := (auMLe p α hα hαp).2
  have hLr : (auL p α : ℝ) ≤ 4 * (p:ℝ) + 1 := by exact_mod_cast hL
  have hkey : (32:ℝ) * (p:ℝ) + 16 ≤ (2:ℝ)^p := auPowTwoGeLinear p hp
  calc (2:ℝ) * (auL p α : ℝ) + 2 ≤ 2 * (4*(p:ℝ)+1) + 2 := by linarith
    _ ≤ (2:ℝ)^p / 4 := by linarith

end Work.Resample
