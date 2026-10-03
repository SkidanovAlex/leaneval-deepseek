import Mathlib
import Submission.Work.FIArea7.MSmoothDefs

namespace Work.FIArea7

/-- `xp p = p ^ (-(1/4))`: the negative-exponent form of the prime weight. -/
lemma xp_eq_rpow_neg (p : ℕ) : xp p = (p : ℝ) ^ (-((1 : ℝ) / 4)) := by
  rw [xp]
  exact (Real.rpow_neg (by positivity : (0 : ℝ) ≤ (p : ℝ)) ((1 : ℝ) / 4)).symm

/-- For every prime `p` (in particular `p ≤ 23`), the prime weight `xp p = p^{-1/4}`
is at most `841/1000`.  The bound is attained at `p = 2`, where `2^{-1/4} ≈ 0.8409`. -/
lemma xp_le_of_prime_le_23 (p : ℕ) (hp : p.Prime) (hp23 : p ≤ 23) : xp p ≤ 841 / 1000 := by
  have h1 : xp p ≤ xp 2 := by
    rw [xp_eq_rpow_neg p, xp_eq_rpow_neg 2]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hp.two_le) (by norm_num : -((1 : ℝ) / 4) ≤ 0)
  have h2 : xp 2 ≤ 841 / 1000 := by
    rw [xp_eq_rpow_neg 2]
    have hlhs : ((2 : ℝ) ^ (-((1 : ℝ) / 4))) ^ (4 : ℝ) = 1 / 2 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (-((1 : ℝ) / 4)) 4]
      rw [show (-((1 : ℝ) / 4)) * 4 = -1 by norm_num, Real.rpow_neg_one]
      norm_num
    have h4 : ((2 : ℝ) ^ (-((1 : ℝ) / 4))) ^ (4 : ℝ) ≤ ((841 : ℝ) / 1000) ^ (4 : ℝ) := by
      rw [hlhs, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    exact (Real.rpow_le_rpow_iff (by positivity) (by norm_num)
      (by norm_num : (0 : ℝ) < 4)).mp h4
  linarith

end Work.FIArea7
