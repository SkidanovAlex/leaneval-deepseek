import Submission.Work.ConeSwitch.MathlibNoHG

namespace Work.Deep.Conc.BruhnJoos

open scoped BigOperators

/-- `exp (n * x) = (exp x) ^ n` for a natural number `n`. -/
private theorem exp_nat_mul (x : ℝ) (n : ℕ) : Real.exp ((n : ℝ) * x) = Real.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ((↑(n + 1) : ℝ) * x) = (n : ℝ) * x + x := by push_cast; ring
    rw [h, Real.exp_add, ih, pow_succ]

/-- `12/5 = 2.4` is a lower bound for `e`.  Obtained from `1 + x ≤ exp x` at `x = 1/4`
(eighth power `(5/4)^4 = 625/256 ≥ 12/5`). -/
private theorem exp_one_ge : (12 / 5 : ℝ) ≤ Real.exp 1 := by
  have h14 : (5 / 4 : ℝ) ≤ Real.exp (1 / 4) := by
    have := Real.add_one_le_exp (1 / 4 : ℝ)
    linarith
  have h4 : Real.exp 1 = Real.exp (1 / 4) ^ 4 := by
    rw [show (1 : ℝ) = 1 / 4 + 1 / 4 + 1 / 4 + 1 / 4 by norm_num]
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    ring_nf
  rw [h4]
  have hpow : (5 / 4 : ℝ) ^ 4 ≤ Real.exp (1 / 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) h14 4
  have hnum : (5 / 4 : ℝ) ^ 4 = 625 / 256 := by norm_num
  rw [hnum] at hpow
  linarith

/-- `4 ≤ e ^ 2`. -/
private theorem exp_two_ge : (4 : ℝ) ≤ Real.exp 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [exp_one_ge]
  have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [hsplit]
  have t1 : (2 : ℝ) * Real.exp 1 ≤ Real.exp 1 * Real.exp 1 :=
    mul_le_mul_of_nonneg_right h2 (Real.exp_pos 1).le
  have t2 : (2 : ℝ) * 2 ≤ (2 : ℝ) * Real.exp 1 :=
    mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- `e⁻¹ ≤ 5/12`. -/
private theorem exp_neg_one_le : Real.exp (-(1 : ℝ)) ≤ 5 / 12 := by
  have hprod : Real.exp 1 * Real.exp (-(1 : ℝ)) = 1 := by
    rw [← Real.exp_add, show (1 : ℝ) + -(1 : ℝ) = 0 by norm_num, Real.exp_zero]
  have hne : (0 : ℝ) ≤ Real.exp (-(1 : ℝ)) := (Real.exp_pos _).le
  have t : (12 / 5 : ℝ) * Real.exp (-(1 : ℝ)) ≤ Real.exp 1 * Real.exp (-(1 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith [exp_one_ge]) hne
  rw [hprod] at t
  linarith

/-- `e⁻² ≤ 1/4`. -/
private theorem exp_neg_two_le : Real.exp (-(2 : ℝ)) ≤ 1 / 4 := by
  have hprod : Real.exp 2 * Real.exp (-(2 : ℝ)) = 1 := by
    rw [← Real.exp_add, show (2 : ℝ) + -(2 : ℝ) = 0 by norm_num, Real.exp_zero]
  have hne : (0 : ℝ) ≤ Real.exp (-(2 : ℝ)) := (Real.exp_pos _).le
  have t : (4 : ℝ) * Real.exp (-(2 : ℝ)) ≤ Real.exp 2 * Real.exp (-(2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith [exp_two_ge]) hne
  rw [hprod] at t
  linarith

/-- For `k ≥ 2` the term `exp (-k²)` is dominated by `(1/4)^k`: indeed
`k² ≥ 2k`, so `exp (-k²) ≤ (e⁻²)^k ≤ ((1/4))^k`. -/
private theorem exp_neg_sq_le_pow (k : ℕ) (hk : 2 ≤ k) :
    Real.exp (-(k : ℝ) ^ 2) ≤ ((1 / 4 : ℝ)) ^ k := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsq : (2 : ℝ) * (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hkR]
  have h1 : Real.exp (-(k : ℝ) ^ 2) ≤ Real.exp (-(2 : ℝ) * (k : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(2 : ℝ) * (k : ℝ)) = Real.exp (-(2 : ℝ)) ^ k := by
    rw [mul_comm]
    exact exp_nat_mul (-(2 : ℝ)) k
  have h4 : Real.exp (-(2 : ℝ)) ^ k ≤ ((1 / 4 : ℝ)) ^ k :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_two_le k
  exact h1.trans (h2.le.trans h4)

/-- Key quantitative bound: the partial sum up to index `m + 1` is at most
`3/2 - (4/3) (1/4)^(m+2)`, i.e. the geometric tail estimate
`∑_{k ≥ m+2} (1/4)^k = (4/3)(1/4)^(m+2)` is "saved". -/
private theorem sum_bound (m : ℕ) :
    (∑ k ∈ Finset.range (m + 2), Real.exp (-(k : ℝ) ^ 2)) ≤
      3 / 2 - 4 / 3 * ((1 / 4 : ℝ)) ^ (m + 2) := by
  induction m with
  | zero =>
    have hbase : (∑ k ∈ Finset.range 2, Real.exp (-(k : ℝ) ^ 2)) =
        1 + Real.exp (-(1 : ℝ)) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [show (0 + 2 : ℕ) = 2 by norm_num, hbase]
    have ht : (3 : ℝ) / 2 - 4 / 3 * ((1 / 4 : ℝ)) ^ 2 = 17 / 12 := by norm_num
    rw [ht]
    linarith [exp_neg_one_le]
  | succ m ih =>
    rw [show (m + 1 + 2 : ℕ) = (m + 2) + 1 by omega, Finset.sum_range_succ]
    have hf := exp_neg_sq_le_pow (m + 2) (by omega)
    have htail : (3 : ℝ) / 2 - 4 / 3 * ((1 / 4 : ℝ)) ^ ((m + 2) + 1) =
        3 / 2 - (1 / 3) * ((1 / 4 : ℝ)) ^ (m + 2) := by
      rw [pow_succ]
      ring
    rw [htail]
    linarith [ih, hf]

theorem sum_exp_neg_sq_le (n : ℕ) :
    (∑ k ∈ Finset.range n, Real.exp (-(k : ℝ) ^ 2)) ≤ 3 / 2 := by
  match n with
  | 0 =>
    simp only [Finset.range_zero, Finset.sum_empty]
    norm_num
  | 1 =>
    rw [Finset.sum_range_one]
    norm_num
  | m + 2 =>
    have h := sum_bound m
    have hpos : (0 : ℝ) < ((1 / 4 : ℝ)) ^ (m + 2) := pow_pos (by norm_num) _
    linarith [h, hpos]

end Work.Deep.Conc.BruhnJoos
