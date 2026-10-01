import Mathlib
import Submission.Work.ZeroDensity.Ingham.divisorSqSummatory
import Submission.Work.ZeroDensity.Montgomery.divisorsCardDivSum_le
import Submission.Work.ZeroDensity.Ingham.doubleSumReindex
import Submission.Work.ZeroDensity.Ingham.innerHarmonicBound
import Submission.Work.ZeroDensity.Ingham.oneAddLogLeTwoMulLog

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

/-- The pointwise simplification `(D n/√n)^2 · n/(n-m) = (D n)^2/(n-m)` which replaces the weight
`(D n/√n)^2` by the divisor-square `(D n)^2`: `(D n/√n)^2 · n = (D n)^2`, and the two factors of
`n` cancel against the `√n` and against the denominator. -/
private lemma term_eq {m n : ℕ} (h : m + 1 ≤ n) :
    (((Nat.divisors n).card : ℝ) / Real.sqrt (n : ℝ))^2 * ((n : ℝ) / ((n:ℝ) - (m:ℝ)))
      = ((Nat.divisors n).card : ℝ)^2 / ((n:ℝ) - (m:ℝ)) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hmn : ((n:ℝ) - (m:ℝ)) ≠ 0 := by
    have : (m:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : m < n)
    linarith
  rw [div_pow, Real.sq_sqrt hn0.le]
  field_simp

/-- Interchange the two sums and use `(D n/√n)^2 · n = D n^2`: the sum equals
`∑_{n≤N} D n^2 · ∑_{m=1}^{n-1} 1/(n-m) = ∑_{n≤N} D n^2 · H_{n-1} ≤ (1+log N) ∑ D n^2`, then bound
with `Work.ZeroDensity.Ingham.divisorSqSummatory` (`∑ D n^2 ≪ N log^3(2N)`) and the harmonic bound
`Work.ZeroDensity.Montgomery.sum_Ioc_inv_le_one_add_log`. Here `D n = (Nat.divisors n).card`. -/
theorem upperTermTwoBound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N,
        (((Nat.divisors n).card : ℝ) / Real.sqrt (n : ℝ))^2 * ((n : ℝ) / ((n:ℝ) - (m:ℝ))))
      ≤ C * (N : ℝ) * (Real.log (2 * (N : ℝ)))^4 := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroDensity.Ingham.divisorSqSummatory
  refine ⟨2 * C, by linarith, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hlog2 : 0 ≤ Real.log (2 * (N:ℝ)) := Real.log_nonneg (by linarith)
  have hlog1 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNR
  -- Step 1: pointwise replacement of the weight `(D n/√n)^2 · n/(n-m)` by `(D n)^2/(n-m)`.
  have hstep1 : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N,
        (((Nat.divisors n).card : ℝ) / Real.sqrt (n : ℝ))^2 * ((n : ℝ) / ((n:ℝ) - (m:ℝ))))
      = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N,
        ((Nat.divisors n).card : ℝ)^2 / ((n:ℝ) - (m:ℝ))) :=
    Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl
      (fun n hn => term_eq (Finset.mem_Icc.mp hn).1))
  -- Step 2: interchange the two sums (upper triangle `∑_{m<n}` becomes `∑_{n} ∑_{m<n}`).
  rw [hstep1, doubleSumReindex N (fun m n => ((Nat.divisors n).card : ℝ)^2 / ((n:ℝ) - (m:ℝ)))]
  -- Step 3: factor `(D n)^2` out of the inner sum over `m`.
  have hfac : (∑ n ∈ Finset.Ico 1 (N+1), ∑ m ∈ Finset.Ico 1 n,
        ((Nat.divisors n).card : ℝ)^2 / ((n:ℝ) - (m:ℝ)))
      = ∑ n ∈ Finset.Ico 1 (N+1),
          ((Nat.divisors n).card : ℝ)^2 * (∑ m ∈ Finset.Ico 1 n, (1:ℝ) / ((n:ℝ) - (m:ℝ))) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [hfac]
  -- Step 4: bound the inner harmonic sum by `1 + log N`, then the divisor-square sum.
  calc ∑ n ∈ Finset.Ico 1 (N+1),
        ((Nat.divisors n).card : ℝ)^2 * (∑ m ∈ Finset.Ico 1 n, (1:ℝ) / ((n:ℝ) - (m:ℝ)))
      ≤ ∑ n ∈ Finset.Ico 1 (N+1), ((Nat.divisors n).card : ℝ)^2 * (1 + Real.log (N:ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        have h1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
        have h2 : n ≤ N := by have := (Finset.mem_Ico.mp hn).2; omega
        exact mul_le_mul_of_nonneg_left (innerHarmonicBound N n h1 h2) (sq_nonneg _)
    _ = (1 + Real.log (N:ℝ)) * ∑ n ∈ Finset.Ico 1 (N+1), ((Nat.divisors n).card : ℝ)^2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ = (1 + Real.log (N:ℝ)) * ∑ n ∈ Finset.Icc 1 N, ((Nat.divisors n).card : ℝ)^2 := by
        rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ (1 + Real.log (N:ℝ)) * (C * (N:ℝ) * (Real.log (2*(N:ℝ)))^3) := by
        apply mul_le_mul_of_nonneg_left (hC N hN1) (by linarith)
    _ ≤ (2 * Real.log (2*(N:ℝ))) * (C * (N:ℝ) * (Real.log (2*(N:ℝ)))^3) := by
        apply mul_le_mul_of_nonneg_right (oneAddLogLeTwoMulLog N hN)
        exact mul_nonneg (mul_nonneg (le_of_lt hCpos) (Nat.cast_nonneg N)) (pow_nonneg hlog2 3)
    _ = (2*C) * (N:ℝ) * (Real.log (2*(N:ℝ)))^4 := by ring

end Work.ZeroDensity.Ingham
