import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.divisors_pair_reindex

namespace Work.FIArea7

open Finset
open scoped BigOperators

/-- **Pointwise Möbius identity.**  For `1 ≤ c` and `1 ≤ ℓ`, `μ(c ℓ) · μ(c)` equals `μ(c)² · μ(ℓ)`
when `c` and `ℓ` are coprime, and `0` when they are not: if a prime divides both, then `c ℓ` is not
squarefree so `μ(c ℓ) = 0`. -/
lemma moebius_mul_moebius_pair (c ℓ : ℕ) (hc : 1 ≤ c) (hℓ : 1 ≤ ℓ) :
    (ArithmeticFunction.moebius (c * ℓ) : ℂ) * (ArithmeticFunction.moebius c : ℂ)
      = (if Nat.Coprime c ℓ then
          (ArithmeticFunction.moebius c : ℂ) ^ 2 * (ArithmeticFunction.moebius ℓ : ℂ) else 0) := by
  by_cases h : Nat.Coprime c ℓ
  · rw [if_pos h,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (Nat.coprime_iff_gcd_eq_one.mp h)]
    push_cast
    ring
  · rw [if_neg h]
    have hnsf : ¬ Squarefree (c * ℓ) := by
      intro hsf
      have hgcd : c.gcd ℓ ≠ 1 := fun h1 => h (Nat.coprime_iff_gcd_eq_one.mpr h1)
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
      have hpc : p ∣ c := dvd_trans hpdvd (Nat.gcd_dvd_left c ℓ)
      have hpℓ : p ∣ ℓ := dvd_trans hpdvd (Nat.gcd_dvd_right c ℓ)
      have hp2 : p * p ∣ c * ℓ := by
        obtain ⟨c', rfl⟩ := hpc
        obtain ⟨ℓ', rfl⟩ := hpℓ
        exact ⟨c' * ℓ', by ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp) hp2
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
    simp

/-- **Pointwise Möbius identity, weighted form.**  The exact shape of one summand that identifies
the `(n, d)` double sum of `gammaSwap` with its `(c, ℓ)` double sum. -/
lemma moebius_pair_term (c ℓ : ℕ) (hc : 1 ≤ c) (hℓ : 1 ≤ ℓ) (w : ℕ → ℂ) (X : ℕ → ℂ) :
    w (c * ℓ) * (ArithmeticFunction.moebius (c * ℓ) : ℂ) * (ArithmeticFunction.moebius c : ℂ) * X (c * ℓ)
      = (if Nat.Coprime c ℓ then
          (ArithmeticFunction.moebius c : ℂ) ^ 2
            * ((ArithmeticFunction.moebius ℓ : ℂ) * w (c * ℓ) * X (c * ℓ)) else 0) := by
  rw [mul_assoc (w (c * ℓ)) (ArithmeticFunction.moebius (c * ℓ) : ℂ) (ArithmeticFunction.moebius c : ℂ),
    moebius_mul_moebius_pair c ℓ hc hℓ]
  by_cases h : Nat.Coprime c ℓ
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- **(*FI* 25.2): the Möbius expansion of `γ` and the exchange of summation.**  With
`γ(n;C) = Σ_{c ∣ n, c ≤ C} μ(c)` (`Work.FIPlan.gammaTrunc`), an arbitrary weight `w` supported on
`[1,T]` and an arbitrary factor `X`, the sum `Σ_{n ≤ T} w n · μ(n) γ(n;C) X n` equals the double
sum over the squarefree `c ≤ C` and over `ℓ ≤ T` coprime to `c`:
`μ(n) = μ(c)μ(ℓ)` on coprime factors, and `Σ_{c|n, c ≤ C} μ(c)` is the definition of `γ`.
The support hypothesis `hw` is what allows the inner `ℓ`-sum to be extended to all `ℓ ≤ T`
(terms with `c ℓ > T` vanish). -/
theorem gammaSwap (w : ℕ → ℂ) (Cc : ℝ) (T : ℕ) (X : ℕ → ℂ) (hCc1 : 1 ≤ Cc) (hT : 1 ≤ T)
    (hw : ∀ n : ℕ, T < n → w n = 0) :
    (∑ n ∈ Finset.Icc 1 T,
        w n * (ArithmeticFunction.moebius n : ℂ) * ((Work.FIPlan.gammaTrunc Cc n : ℝ) : ℂ) * X n)
      = ∑ c ∈ (Finset.Icc 1 T).filter (fun c : ℕ => (c : ℝ) ≤ Cc),
          (ArithmeticFunction.moebius c : ℂ) ^ 2 *
            ∑ ℓ ∈ Finset.Icc 1 T,
              (if Nat.Coprime c ℓ then
                (ArithmeticFunction.moebius ℓ : ℂ) * w (c * ℓ) * X (c * ℓ) else 0) := by
  -- Step 1: expand `γ` and reindex the `(n, d)` double sum as a `(d, ℓ)` double sum.
  have hL : (∑ n ∈ Finset.Icc 1 T,
        w n * (ArithmeticFunction.moebius n : ℂ) * ((Work.FIPlan.gammaTrunc Cc n : ℝ) : ℂ) * X n)
      = ∑ d ∈ (Finset.Icc 1 T).filter (fun d : ℕ => (d : ℝ) ≤ Cc),
          ∑ ℓ ∈ Finset.Icc 1 T,
            w (d * ℓ) * (ArithmeticFunction.moebius (d * ℓ) : ℂ) * (ArithmeticFunction.moebius d : ℂ)
              * X (d * ℓ) := by
    calc ∑ n ∈ Finset.Icc 1 T,
        w n * (ArithmeticFunction.moebius n : ℂ) * ((Work.FIPlan.gammaTrunc Cc n : ℝ) : ℂ) * X n
        = ∑ n ∈ Finset.Icc 1 T, ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
            w n * (ArithmeticFunction.moebius n : ℂ) * (ArithmeticFunction.moebius d : ℂ) * X n := by
          refine Finset.sum_congr rfl ?_
          intro n _
          rw [Work.FIPlan.gammaTrunc, Complex.ofReal_sum]
          simp only [Complex.ofReal_intCast]
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ d ∈ (Finset.Icc 1 T).filter (fun d : ℕ => (d : ℝ) ≤ Cc),
          ∑ ℓ ∈ Finset.Icc 1 T,
            w (d * ℓ) * (ArithmeticFunction.moebius (d * ℓ) : ℂ) * (ArithmeticFunction.moebius d : ℂ)
              * X (d * ℓ) :=
          divisors_pair_reindex T Cc
            (fun n d => w n * (ArithmeticFunction.moebius n : ℂ) * (ArithmeticFunction.moebius d : ℂ) * X n)
            (fun d ℓ h => by simp [hw (d * ℓ) h])
  -- Step 2: absorb the squared Möbius factor into the inner `ℓ`-sum on the right-hand side.
  have hR : (∑ c ∈ (Finset.Icc 1 T).filter (fun c : ℕ => (c : ℝ) ≤ Cc),
          (ArithmeticFunction.moebius c : ℂ) ^ 2 *
            ∑ ℓ ∈ Finset.Icc 1 T,
              (if Nat.Coprime c ℓ then
                (ArithmeticFunction.moebius ℓ : ℂ) * w (c * ℓ) * X (c * ℓ) else 0))
      = ∑ c ∈ (Finset.Icc 1 T).filter (fun c : ℕ => (c : ℝ) ≤ Cc),
          ∑ ℓ ∈ Finset.Icc 1 T,
            (if Nat.Coprime c ℓ then
              (ArithmeticFunction.moebius c : ℂ) ^ 2
                * ((ArithmeticFunction.moebius ℓ : ℂ) * w (c * ℓ) * X (c * ℓ)) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ℓ _
    by_cases h : Nat.Coprime c ℓ <;> simp [h]
  rw [hL, hR]
  -- Step 3: match the two double sums term by term.
  refine Finset.sum_congr rfl ?_
  intro c hc
  refine Finset.sum_congr rfl ?_
  intro ℓ hℓ
  exact moebius_pair_term c ℓ (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
    (Finset.mem_Icc.mp hℓ).1 w X

end Work.FIArea7
