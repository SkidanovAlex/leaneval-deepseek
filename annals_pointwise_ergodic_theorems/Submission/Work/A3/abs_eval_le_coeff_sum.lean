import Mathlib
import Submission.Work.A3.Defs

namespace Work.A3

theorem abs_eval_le_coeff_sum (Q : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) {n : ℤ}
    (hn : n ∈ Finset.Icc (1 : ℤ) (N : ℤ)) :
    |Q.eval n| ≤ (∑ j ∈ Q.support, |Q.coeff j|) * (N : ℤ) ^ Q.natDegree := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℤ) ≤ n := le_trans (by norm_num) hn1
  have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  rw [Polynomial.eval_eq_sum]
  calc |∑ j ∈ Q.support, Q.coeff j * n ^ j|
      ≤ ∑ j ∈ Q.support, |Q.coeff j * n ^ j| :=
        Finset.abs_sum_le_sum_abs (fun j => Q.coeff j * n ^ j) Q.support
    _ = ∑ j ∈ Q.support, |Q.coeff j| * n ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [abs_mul, abs_of_nonneg (pow_nonneg hn0 j)]
    _ ≤ ∑ j ∈ Q.support, |Q.coeff j| * (N : ℤ) ^ Q.natDegree := by
        refine Finset.sum_le_sum ?_
        intro j hj
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hjle : j ≤ Q.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
        calc n ^ j ≤ (N : ℤ) ^ j := pow_le_pow_left₀ hn0 hnN j
          _ ≤ (N : ℤ) ^ Q.natDegree := pow_le_pow_right₀ hN1 hjle
    _ = (∑ j ∈ Q.support, |Q.coeff j|) * (N : ℤ) ^ Q.natDegree := by
        rw [Finset.sum_mul]

end Work.A3
