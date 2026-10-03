import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.sum_tau_pow_div_le

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators
/-- Hint: `φ(g) ≤ g` (`Nat.totient_le`), so the summand is `≤ τ(g)⁴/g`; apply
`Work.FIArea2.sum_tau_pow_div_le 4` (`Σ_{n ≤ R} τ(n)⁴/n ≤ C(log R + 2)^{16}`, `2^4 = 16`). -/
theorem phi_tau4_div_dsum :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ,
      (∑ g ∈ Finset.Icc 1 R,
          (Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) ^ 2)
        ≤ C * (Real.log ((R : ℝ) + 2) + 2) ^ 16 := by
  obtain ⟨C, hCpos, hC⟩ := Work.FIArea2.sum_tau_pow_div_le 4
  refine ⟨C, hCpos, fun R => ?_⟩
  -- pointwise: `φ(g)·τ(g)⁴/g² ≤ τ(g)⁴/g` for `g ≥ 1`
  have hsum : (∑ g ∈ Finset.Icc 1 R,
          (Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) ^ 2)
        ≤ ∑ g ∈ Finset.Icc 1 R, ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) := by
    apply Finset.sum_le_sum
    intro g hg
    have hg1 : 1 ≤ g := (Finset.mem_Icc.mp hg).1
    have hgpos : (0 : ℝ) < g := by exact_mod_cast hg1
    have htau : (0 : ℝ) ≤ ((g.divisors.card : ℝ)) ^ 4 := by positivity
    have hphi : (Nat.totient g : ℝ) ≤ (g : ℝ) := by exact_mod_cast Nat.totient_le g
    have hg2 : (0 : ℝ) < (g : ℝ) ^ 2 := by positivity
    have h1 : (Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) ^ 2
        ≤ (g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hphi htau) hg2.le
    have h2 : (g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) ^ 2
        = ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) := by
      field_simp
    rw [h2] at h1
    exact h1
  -- monotonicity of the base: `log R + 2 ≤ log(R+2) + 2`, both nonnegative
  have hbase : (Real.log (R : ℝ) + 2) ^ 16 ≤ (Real.log ((R : ℝ) + 2) + 2) ^ 16 := by
    apply pow_le_pow_left₀
    · rcases Nat.eq_zero_or_pos R with h | h
      · subst h; simp
      · have : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast h)
        linarith
    · rcases Nat.eq_zero_or_pos R with h | h
      · subst h; simp; exact Real.log_nonneg (by norm_num)
      · have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast h
        have hle : (R : ℝ) ≤ (R : ℝ) + 2 := by linarith
        have := Real.log_le_log hRpos hle
        linarith
  calc (∑ g ∈ Finset.Icc 1 R,
          (Nat.totient g : ℝ) * ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) ^ 2)
      ≤ ∑ g ∈ Finset.Icc 1 R, ((g.divisors.card : ℝ)) ^ 4 / (g : ℝ) := hsum
    _ ≤ C * (Real.log (R : ℝ) + 2) ^ 16 := by simpa using hC R
    _ ≤ C * (Real.log ((R : ℝ) + 2) + 2) ^ 16 :=
        mul_le_mul_of_nonneg_left hbase hCpos.le

end Work.FIArea2.R6
