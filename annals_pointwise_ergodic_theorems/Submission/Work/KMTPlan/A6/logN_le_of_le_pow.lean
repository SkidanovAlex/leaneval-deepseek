import Mathlib
import Submission.Work.Analysis.EndVar.Defs

namespace Work.KMTPlan.A6

/-- The logarithmic scale `Log N = log₂ max(N,2)` is bounded by any `B ≥ 1` with `N ≤ 2 ^ B`:
`max(N,2) ≤ 2 ^ B < 2 ^ (B+1)`, and `Nat.log 2` is the integer part of `log₂`. -/
theorem logN_le_of_le_pow {N B : ℕ} (hN : N ≤ 2 ^ B) (hB : 1 ≤ B) :
    Work.Analysis.EndVar.logN N ≤ (B : ℤ) := by
  have h2B : 2 ≤ 2 ^ B := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB
  have hmax : max N 2 ≤ 2 ^ B := max_le hN h2B
  have hne : max N 2 ≠ 0 := by omega
  have hlt : max N 2 < 2 ^ (B + 1) :=
    lt_of_le_of_lt hmax (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B))
  have hlog : Nat.log 2 (max N 2) < B + 1 :=
    (Nat.log_lt_iff_lt_pow (by norm_num) hne).mpr hlt
  have hle : Nat.log 2 (max N 2) ≤ B := by omega
  simp only [Work.Analysis.EndVar.logN]
  exact_mod_cast hle

end Work.KMTPlan.A6
