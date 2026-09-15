import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean

namespace Commons.NumberTheory.Sieve

theorem isSmallRat_rat_div {a : ℤ} {n L₀ : ℕ} (hn : 1 ≤ n) (ha : a.natAbs ≤ L₀) (hnL : n ≤ L₀) :
    Commons.NumberTheory.Sieve.IsSmallRat L₀ ((a : ℚ) / (n : ℚ)) := by
  have hn0 : (n : ℤ) ≠ 0 := by omega
  have hq : (a : ℚ) / (n : ℚ) = Rat.divInt a (n : ℤ) := by
    rw [Rat.divInt_eq_div]
    norm_num
  rw [hq, IsSmallRat]
  constructor
  · have hdvd : (Rat.divInt a (n : ℤ)).num.natAbs ∣ a.natAbs :=
      Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd a hn0)
    rcases eq_or_ne a 0 with rfl | ha0
    · have hzero : Rat.divInt (0 : ℤ) (n : ℤ) = 0 := by
        rw [Rat.divInt_eq_div]; simp
      rw [hzero]; simp
    · exact le_trans (Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) hdvd) ha
  · rw [Rat.den_divInt, if_neg hn0, Int.natAbs_natCast]
    exact le_trans (Nat.div_le_self n _) hnL

end Commons.NumberTheory.Sieve
