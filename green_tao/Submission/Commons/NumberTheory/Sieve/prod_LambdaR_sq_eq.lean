import Mathlib
import Submission.Commons.NumberTheory.Sieve.LambdaR_sq_eq_sum_lcm_pos

namespace Commons.NumberTheory.Sieve

theorem prod_LambdaR_sq_eq (R m : ℕ) (n : Fin m → ℕ) (hpos : ∀ i, 0 < n i) : ∏ i, (Commons.NumberTheory.Sieve.LambdaR R (n i)) ^ 2 = ∑ d ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 R), ∑ e ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 R), ∏ i, (((ArithmeticFunction.moebius (d i) : ℤ) : ℝ) * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ) * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ)) * (if Nat.lcm (d i) (e i) ∣ n i then (1:ℝ) else 0)) := by
  classical
  have hfac : ∀ i : Fin m, (Commons.NumberTheory.Sieve.LambdaR R (n i)) ^ 2
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          (if Nat.lcm d e ∣ n i then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ)
              * Real.log ((R : ℝ) / (d : ℝ)) * Real.log ((R : ℝ) / (e : ℝ))
           else 0) := fun i => LambdaR_sq_eq_sum_lcm_pos R (n i) (hpos i)
  simp only [hfac]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases h : Nat.lcm (d i) (e i) ∣ n i
  · simp [h]
  · simp [h]

end Commons.NumberTheory.Sieve
