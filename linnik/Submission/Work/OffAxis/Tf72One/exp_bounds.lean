import Mathlib

namespace Work.OffAxis.Tf72One

/-- Auxiliary glue: if `k * y = x`, `exp y ≤ B` and `B ^ k ≤ q` then `exp x ≤ q`.

This is the only ingredient needed to push the Taylor bounds of `Real.exp_bound'` (which are
stated for arguments in `[0,1]`) up to the larger arguments `6/5, 3/2, 9/5, 21/10, 17/8`: write
`x = k * (x / k)` with `x / k ≤ 1`, bound `exp (x / k)` by the truncated series and raise to the
`k`-th power. -/
private lemma exp_le_of_pow {x y B q : ℝ} {k : ℕ}
    (hB : Real.exp y ≤ B) (hq : B ^ k ≤ q) (hxy : (k : ℝ) * y = x) :
    Real.exp x ≤ q := by
  have h : Real.exp x = Real.exp y ^ k := by
    rw [← hxy]
    exact Real.exp_nat_mul y k
  rw [h]
  exact (pow_le_pow_left₀ (Real.exp_nonneg y) hB k).trans hq

/-- Rational upper bounds for `exp` at the nine grid arguments `0, 3/10, 3/5, 9/10, 6/5, 3/2, 9/5,
21/10, 17/8`. -/
theorem exp_bounds :
    Real.exp (0:ℝ) ≤ 1 ∧
    Real.exp ((3:ℝ)/10) ≤ (134986/100000 : ℝ) ∧
    Real.exp ((3:ℝ)/5) ≤ (182212/100000 : ℝ) ∧
    Real.exp ((9:ℝ)/10) ≤ (245961/100000 : ℝ) ∧
    Real.exp ((6:ℝ)/5) ≤ (332012/100000 : ℝ) ∧
    Real.exp ((3:ℝ)/2) ≤ (448170/100000 : ℝ) ∧
    Real.exp ((9:ℝ)/5) ≤ (604965/100000 : ℝ) ∧
    Real.exp ((21:ℝ)/10) ≤ (816618/100000 : ℝ) ∧
    Real.exp ((17:ℝ)/8) ≤ (83729/10000 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Real.exp_zero]
  · -- exp(3/10), Taylor order 6 at 3/10
    refine (Real.exp_bound' (x := (3:ℝ)/10) (by norm_num) (by norm_num) (n := 6)
      (by norm_num)).trans ?_
    norm_num [Finset.sum_range_succ]
  · -- exp(3/5), Taylor order 7 at 3/5
    refine (Real.exp_bound' (x := (3:ℝ)/5) (by norm_num) (by norm_num) (n := 7)
      (by norm_num)).trans ?_
    norm_num [Finset.sum_range_succ]
  · -- exp(9/10), Taylor order 7 at 9/10
    refine (Real.exp_bound' (x := (9:ℝ)/10) (by norm_num) (by norm_num) (n := 7)
      (by norm_num)).trans ?_
    norm_num [Finset.sum_range_succ]
  · -- exp(6/5) = exp(3/5)^2, Taylor order 7 at 3/5
    refine exp_le_of_pow (k := 2) (y := (3:ℝ)/5)
      (Real.exp_bound' (x := (3:ℝ)/5) (by norm_num) (by norm_num) (n := 7) (by norm_num))
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
  · -- exp(3/2) = exp(3/4)^2, Taylor order 7 at 3/4
    refine exp_le_of_pow (k := 2) (y := (3:ℝ)/4)
      (Real.exp_bound' (x := (3:ℝ)/4) (by norm_num) (by norm_num) (n := 7) (by norm_num))
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
  · -- exp(9/5) = exp(9/10)^2, Taylor order 8 at 9/10
    refine exp_le_of_pow (k := 2) (y := (9:ℝ)/10)
      (Real.exp_bound' (x := (9:ℝ)/10) (by norm_num) (by norm_num) (n := 8) (by norm_num))
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
  · -- exp(21/10) = exp(7/10)^3, Taylor order 7 at 7/10
    refine exp_le_of_pow (k := 3) (y := (7:ℝ)/10)
      (Real.exp_bound' (x := (7:ℝ)/10) (by norm_num) (by norm_num) (n := 7) (by norm_num))
      (by norm_num [Finset.sum_range_succ]) (by norm_num)
  · -- exp(17/8) = exp(17/24)^3, Taylor order 8 at 17/24
    refine exp_le_of_pow (k := 3) (y := (17:ℝ)/24)
      (Real.exp_bound' (x := (17:ℝ)/24) (by norm_num) (by norm_num) (n := 8) (by norm_num))
      (by norm_num [Finset.sum_range_succ]) (by norm_num)

end Work.OffAxis.Tf72One
