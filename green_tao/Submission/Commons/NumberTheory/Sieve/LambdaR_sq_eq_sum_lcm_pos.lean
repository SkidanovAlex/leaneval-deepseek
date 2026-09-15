import Mathlib
import Submission.Commons.NumberTheory.Sieve.LambdaR_prime

namespace Commons.NumberTheory.Sieve

theorem LambdaR_sq_eq_sum_lcm_pos (R n : ℕ) (hn : 0 < n) :
    (Commons.NumberTheory.Sieve.LambdaR R n) ^ 2
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          (if Nat.lcm d e ∣ n then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ)
              * Real.log ((R : ℝ) / (d : ℝ)) * Real.log ((R : ℝ) / (e : ℝ))
           else 0) := by
  have hfinset :
      n.divisors.filter (fun d => d ≤ R) = (Finset.Icc 1 R).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, _⟩, hdR⟩
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
      exact ⟨⟨by omega, hdR⟩, hdn⟩
    · rintro ⟨⟨_, hdR⟩, hdn⟩
      exact ⟨⟨hdn, Nat.pos_iff_ne_zero.mp hn⟩, hdR⟩
  rw [LambdaR, hfinset, Finset.sum_filter, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hdn : d ∣ n
  · by_cases hen : e ∣ n
    · rw [if_pos hdn, if_pos hen, if_pos (Nat.lcm_dvd hdn hen)]
      ring
    · rw [if_pos hdn, if_neg hen,
          if_neg (fun h => hen (Nat.lcm_dvd_iff.mp h).2)]
      ring
  · rw [if_neg hdn, if_neg (fun h => hdn (Nat.lcm_dvd_iff.mp h).1)]
    ring

end Commons.NumberTheory.Sieve
