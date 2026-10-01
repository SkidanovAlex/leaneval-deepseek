import Mathlib
import Submission.Commons.NumberTheory.Sieve.selberg_double_sum_diagonalization

namespace Work.ZeroDensity.Jutila

open Finset

/-- **Bilinear gcd diagonalization.**  For a finite set `T` of positive integers closed under
divisors and any weights `a, b : ℕ → ℝ`,

  `∑_{d,e ∈ T} a_d b_e gcd(d,e) = ∑_{l ∈ T} φ(l) (∑_{d ∈ T, l ∣ d} a_d)(∑_{e ∈ T, l ∣ e} b_e)`,

by expanding `gcd d e = ∑_{l ∣ d, l ∣ e} φ(l)` and exchanging the order of summation.  This is the
bilinear refinement of `Commons.NumberTheory.Sieve.sum_gcd_eq_sum_totient_sq`; if the workspace
module `Submission.Commons.NumberTheory.Sieve.selberg_double_sum_diagonalization` can be imported,
the auxiliary facts `totient_sum_eq_gcd` (the divisor-sum identity for `gcd`) and `sum_sum_ite`
(the `a = b` case of the product factorization) there are exactly what is needed; otherwise
reprove those two small facts locally. -/
lemma gcdBilinearDiagonalization (T : Finset ℕ) (hTpos : ∀ d ∈ T, 0 < d)
    (hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ T → l ∈ T) (a b : ℕ → ℝ) :
    (∑ d ∈ T, ∑ e ∈ T, a d * b e * (Nat.gcd d e : ℝ))
      = ∑ l ∈ T, (Nat.totient l : ℝ) * (∑ d ∈ T.filter (fun d => l ∣ d), a d)
          * (∑ e ∈ T.filter (fun e => l ∣ e), b e) := by
  have step1 : (∑ d ∈ T, ∑ e ∈ T, a d * b e * (Nat.gcd d e : ℝ))
      = ∑ d ∈ T, ∑ e ∈ T, a d * b e *
          (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    rw [Commons.NumberTheory.Sieve.totient_sum_eq_gcd hTpos hTclosed hd he]
  rw [step1]
  have step2 : (∑ d ∈ T, ∑ e ∈ T, a d * b e *
        (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0))
      = ∑ l ∈ T, (Nat.totient l : ℝ) * (∑ d ∈ T.filter (fun d => l ∣ d), a d)
          * (∑ e ∈ T.filter (fun e => l ∣ e), b e) := by
    calc (∑ d ∈ T, ∑ e ∈ T, a d * b e *
            (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0))
        = ∑ d ∈ T, ∑ e ∈ T, ∑ l ∈ T, a d * b e *
            (if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro e _
          rw [Finset.mul_sum]
      _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T, a d * b e *
            (if (l ∣ d ∧ l ∣ e) then (Nat.totient l : ℝ) else 0) := by
          rw [Commons.NumberTheory.Sieve.triple_sum_swap]
      _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T,
            (Nat.totient l : ℝ) * (if l ∣ d then a d else 0)
              * (if l ∣ e then b e else 0) := by
          apply Finset.sum_congr rfl; intro l _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro e _
          by_cases hd : l ∣ d <;> by_cases he : l ∣ e <;> simp [hd, he] <;> ring
      _ = ∑ l ∈ T, (Nat.totient l : ℝ) * (∑ d ∈ T.filter (fun d => l ∣ d), a d)
            * (∑ e ∈ T.filter (fun e => l ∣ e), b e) := by
          apply Finset.sum_congr rfl; intro l _
          have hfac : (∑ d ∈ T, ∑ e ∈ T, (Nat.totient l : ℝ) * (if l ∣ d then a d else 0)
                * (if l ∣ e then b e else 0))
              = (∑ d ∈ T, (Nat.totient l : ℝ) * (if l ∣ d then a d else 0))
                * (∑ e ∈ T, if l ∣ e then b e else 0) :=
            (Finset.sum_mul_sum T T _ _).symm
          rw [hfac, ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.sum_filter]
  rw [step2]

end Work.ZeroDensity.Jutila
