import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Choose.Sum

namespace Commons.Analysis.SpecialFunctions

/-- For natural numbers `j, d`, `(j + d)! ≤ j! · (j + d)^d`: the ratio
`(j+d)!/j! = (j+1)(j+2)⋯(j+d)` is a product of `d` factors each `≤ j+d`. -/
lemma factorial_add_le (j d : ℕ) : (j + d).factorial ≤ j.factorial * (j + d) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : (j + (d + 1)).factorial = (j + d + 1) * (j + d).factorial := by
      rw [show j + (d + 1) = j + d + 1 by omega, Nat.factorial_succ]
    rw [h1]
    calc (j + d + 1) * (j + d).factorial
        ≤ (j + d + 1) * (j.factorial * (j + d) ^ d) := Nat.mul_le_mul_left _ ih
      _ ≤ (j + d + 1) * (j.factorial * (j + d + 1) ^ d) := by
            apply Nat.mul_le_mul_left
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_left (by omega) d
      _ = j.factorial * (j + d + 1) ^ (d + 1) := by rw [pow_succ]; ring
      _ = j.factorial * (j + (d + 1)) ^ (d + 1) := by
            rw [show j + d + 1 = j + (d + 1) by omega]

/-- `n! ≤ j! · n^(n-j)` for `j ≤ n`. -/
lemma factorial_le_factorial_mul_pow (j n : ℕ) (h : j ≤ n) :
    n.factorial ≤ j.factorial * n ^ (n - j) := by
  have key := factorial_add_le j (n - j)
  rwa [Nat.add_sub_cancel' h] at key

/-- The binomial-type estimate with `j` ranging up to `n`:
`∑_{j=0}^{n} C(n,j) t^j / j! ≤ (t + n)^n / n!` for `t ≥ 0`. -/
theorem choose_pow_div_factorial_le_aux (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range (n + 1), (((n.choose j : ℕ)) : ℝ) * t ^ j / (((j.factorial : ℕ)) : ℝ))
      ≤ (t + ((n : ℕ) : ℝ)) ^ n / ((((n.factorial : ℕ)) : ℝ)) := by
  have hpow : (t + ((n : ℕ) : ℝ)) ^ n
      = ∑ j ∈ Finset.range (n + 1), t ^ j * (n : ℝ) ^ (n - j) * (((n.choose j : ℕ)) : ℝ) := by
    rw [add_pow]
  rw [hpow, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_range] at hj
  have hjn : j ≤ n := by omega
  have hfac : ((n.factorial : ℕ) : ℝ) ≤ ((j.factorial : ℕ) : ℝ) * (n : ℝ) ^ (n - j) := by
    exact_mod_cast factorial_le_factorial_mul_pow j n hjn
  have hdenL : (0 : ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hdenR : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_div_iff₀ hdenL hdenR]
  have hA : (0 : ℝ) ≤ (((n.choose j : ℕ)) : ℝ) * t ^ j :=
    mul_nonneg (by positivity) (pow_nonneg ht j)
  calc (((n.choose j : ℕ)) : ℝ) * t ^ j * ((n.factorial : ℕ) : ℝ)
      ≤ ((((n.choose j : ℕ)) : ℝ) * t ^ j)
          * (((j.factorial : ℕ) : ℝ) * (n : ℝ) ^ (n - j)) :=
        mul_le_mul_of_nonneg_left hfac hA
    _ = (t ^ j * (n : ℝ) ^ (n - j) * (((n.choose j : ℕ)) : ℝ))
          * ((j.factorial : ℕ) : ℝ) := by ring

theorem choose_pow_div_factorial_le (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range k, (((k - 1).choose j : ℕ) : ℝ) * t ^ j / (((j.factorial : ℕ) : ℝ))) ≤
      (t + ((k - 1 : ℕ) : ℝ)) ^ (k - 1) / ((((k - 1).factorial : ℕ) : ℝ)) := by
  rcases k with _ | m
  · simp
  · simpa using choose_pow_div_factorial_le_aux m t ht

end Commons.Analysis.SpecialFunctions