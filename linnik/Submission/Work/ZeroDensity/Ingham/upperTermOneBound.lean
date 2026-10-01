import Mathlib
import Submission.Work.ZeroDensity.Ingham.divisorSqSummatory
import Submission.Work.ZeroDensity.Montgomery.divisorSqSum
import Submission.Work.ZeroDensity.Montgomery.divisorsCardDivSum_le
import Submission.Work.ZeroDensity.Ingham.innerSumRatioBound
import Submission.Work.ZeroDensity.Ingham.upperTermOneArith

namespace Work.ZeroDensity.Ingham

/-- For fixed `m`, `∑_{n=m+1}^N n/(n-m) ≤ N + m(1+log N)`: write `n/(n-m) = 1 + m/(n-m)`,
reindex `n ↦ n-m` and use `Work.ZeroDensity.Montgomery.sum_Ioc_inv_le_one_add_log`
(`∑_{d∈Ioc 0 M} 1/d ≤ 1 + log M`). Then `(D m / √m)^2 = D m^2/m` and `(D m/√m)^2 * m = D m^2`,
so the double sum is at most `N * ∑ D m^2/m + (1+log N) * ∑ D m^2`, bounded with
`Work.ZeroDensity.Montgomery.divisorSqSum` (`∑ D m^2/m ≪ log^4(2N)`) and
`Work.ZeroDensity.Ingham.divisorSqSummatory` (`∑ D m^2 ≪ N log^3(2N)`), where
`D m = (Nat.divisors m).card`. -/
theorem upperTermOneBound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N,
        (((Nat.divisors m).card : ℝ) / Real.sqrt (m : ℝ))^2 * ((n : ℝ) / ((n:ℝ) - (m:ℝ))))
      ≤ C * (N : ℝ) * (Real.log (2 * (N : ℝ)))^4 := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.ZeroDensity.Montgomery.divisorSqSum
  obtain ⟨C2, hC2pos, hC2⟩ := Work.ZeroDensity.Ingham.divisorSqSummatory
  refine ⟨C1 + 3*C2, by positivity, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  -- Step 1: bound the inner sum for each fixed `m` and factor out the constant.
  have hstep1 : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N,
        (((Nat.divisors m).card : ℝ) / Real.sqrt (m : ℝ))^2 * ((n : ℝ) / ((n:ℝ) - (m:ℝ))))
      ≤ ∑ m ∈ Finset.Icc 1 N,
          (((Nat.divisors m).card : ℝ)^2 / (m:ℝ)) * ((N : ℝ) + (m:ℝ) * (1 + Real.log (N:ℝ))) := by
    apply Finset.sum_le_sum
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hs : ∀ n : ℕ, (((Nat.divisors m).card : ℝ) / Real.sqrt (m : ℝ))^2 * ((n : ℝ) / ((n:ℝ) - (m:ℝ)))
        = (((Nat.divisors m).card : ℝ)^2 / (m:ℝ)) * ((n : ℝ) / ((n:ℝ) - (m:ℝ))) := by
      intro n
      rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (m:ℝ))]
    rw [Finset.sum_congr rfl (fun n _ => hs n), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (innerSumRatioBound m N hm1 hmN) (by positivity)
  -- Step 2: split the summand into the `N·D m^2/m` part and the `(1+log N)·D m^2` part.
  have hstep2 : ∑ m ∈ Finset.Icc 1 N,
          (((Nat.divisors m).card : ℝ)^2 / (m:ℝ)) * ((N : ℝ) + (m:ℝ) * (1 + Real.log (N:ℝ)))
      = (N:ℝ) * (∑ m ∈ Finset.Icc 1 N, ((Nat.divisors m).card : ℝ)^2 / (m:ℝ))
        + (1 + Real.log (N:ℝ)) * (∑ m ∈ Finset.Icc 1 N, ((Nat.divisors m).card : ℝ)^2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmne : (m:ℝ) ≠ 0 := by positivity
    field_simp
  -- Step 3: apply the two asymptotic inputs and the arithmetic lemma.
  have hL0 : 0 ≤ 1 + Real.log (N:ℝ) := by
    have : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
    linarith
  have hmul1 : (N:ℝ) * (∑ m ∈ Finset.Icc 1 N, ((Nat.divisors m).card : ℝ)^2 / (m:ℝ))
      ≤ (N:ℝ) * (C1 * (Real.log (2 * (N:ℝ)))^4) :=
    mul_le_mul_of_nonneg_left (hC1 N hN1) (by positivity)
  have hmul2 : (1 + Real.log (N:ℝ)) * (∑ m ∈ Finset.Icc 1 N, ((Nat.divisors m).card : ℝ)^2)
      ≤ (1 + Real.log (N:ℝ)) * (C2 * (N:ℝ) * (Real.log (2 * (N:ℝ)))^3) :=
    mul_le_mul_of_nonneg_left (hC2 N hN1) hL0
  calc (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N,
        (((Nat.divisors m).card : ℝ) / Real.sqrt (m : ℝ))^2 * ((n : ℝ) / ((n:ℝ) - (m:ℝ))))
      ≤ ∑ m ∈ Finset.Icc 1 N,
          (((Nat.divisors m).card : ℝ)^2 / (m:ℝ)) * ((N : ℝ) + (m:ℝ) * (1 + Real.log (N:ℝ))) := hstep1
    _ = (N:ℝ) * (∑ m ∈ Finset.Icc 1 N, ((Nat.divisors m).card : ℝ)^2 / (m:ℝ))
        + (1 + Real.log (N:ℝ)) * (∑ m ∈ Finset.Icc 1 N, ((Nat.divisors m).card : ℝ)^2) := hstep2
    _ ≤ (N:ℝ) * (C1 * (Real.log (2 * (N:ℝ)))^4)
        + (1 + Real.log (N:ℝ)) * (C2 * (N:ℝ) * (Real.log (2 * (N:ℝ)))^3) := add_le_add hmul1 hmul2
    _ ≤ (C1 + 3*C2) * (N:ℝ) * (Real.log (2 * (N:ℝ)))^4 := upperTermOneArith C1 C2 hC2pos.le N hN

end Work.ZeroDensity.Ingham
