import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower
import Submission.Work.ChenPlan.LinearSieve.FrameworkR

/-!
# The Rosser–Iwaniec `λ⁻` minorant against `multSum`

`Work.ChenPlan.LinearSieve.RI.lamMinus_multSum_le`:
for every `BoundingSieve` `A`, real sift limit `z` and level `D ≥ 0`,

`Σ_{d ∣ P(z)} λ⁻(d) · multSum(d) ≤ S(A, z)`

— *without* any remainder term.  The point is that `multSum d` is the **exact** mass of the
support elements divisible by `d` (`BoundingSieve.multSum`), i.e.
`multSum d = Σ_{n ∈ support, d ∣ n} weights n`.  Exchanging the two sums therefore turns the
left-hand side into `Σ_{n ∈ support} weights n · Wm(gcd n (P(z)), D)`, and the minorant property
`Wm m D ≤ [m = 1]` of `λ⁻` (`lamMinus_moebius_sum_le`) bounds the inner sum by the indicator of
`gcd n (P(z)) = 1`, which is exactly the sifting condition of `siftedSumR A z`.

This is the same computation as the `hbound` step of `lamMinus_sieve_lower`, where the extra
`- remSum A D` is a weakening of the present inequality (`remSum_nonneg`).  Note that no
hypothesis `2 ≤ z` is needed: the argument uses the sieve axiom nowhere.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

theorem lamMinus_multSum_le (A : BoundingSieve) (z D : ℝ) (hD : 0 ≤ D) :
    (∑ d ∈ (Work.ChenPlan.LinearSieve.Pz A z).divisors,
        Work.ChenPlan.LinearSieve.lamMinus (Work.ChenPlan.LinearSieve.Pz A z) D d * A.multSum d)
      ≤ Work.ChenPlan.LinearSieve.siftedSumR A z := by
  have hPz0 : Pz A z ≠ 0 := Pz_ne_zero A z
  have hlam : ∀ d ∈ (Pz A z).divisors,
      lamMinus (Pz A z) D d = (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
    intro d hd
    obtain ⟨hdd, -⟩ := Nat.mem_divisors.mp hd
    rw [lamMinus]
    by_cases h : rdMinus D d
    · rw [if_pos ⟨hdd, h⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.2), if_neg h]
  rw [Finset.sum_congr rfl (fun d hd => by rw [hlam d hd])]
  calc (∑ d ∈ (Pz A z).divisors,
          (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.multSum d)
      = ∑ d ∈ (Pz A z).divisors, ∑ n ∈ A.support,
          (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
            * (if d ∣ n then A.weights n else 0) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [BoundingSieve.multSum, Finset.mul_sum]
    _ = ∑ n ∈ A.support, ∑ d ∈ (Pz A z).divisors,
          (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
            * (if d ∣ n then A.weights n else 0) :=
        Finset.sum_comm
    _ ≤ ∑ n ∈ A.support, (if Nat.gcd n (Pz A z) = 1 then 1 else 0) * A.weights n := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        have h1 : (∑ d ∈ (Pz A z).divisors,
              (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
                * (if d ∣ n then A.weights n else 0))
            = A.weights n * (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
              (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)) := by
          have hset : (Pz A z).divisors.filter (fun d => d ∣ n) = (Nat.gcd n (Pz A z)).divisors := by
            ext d
            rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
            constructor
            · rintro ⟨⟨h1, -⟩, h2⟩
              exact ⟨Nat.dvd_gcd h2 h1, fun hh => hPz0 (Nat.gcd_eq_zero_iff.mp hh).2⟩
            · rintro ⟨h1, -⟩
              exact ⟨⟨dvd_trans h1 (Nat.gcd_dvd_right n (Pz A z)), hPz0⟩,
                dvd_trans h1 (Nat.gcd_dvd_left n (Pz A z))⟩
          calc (∑ d ∈ (Pz A z).divisors,
                (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
                  * (if d ∣ n then A.weights n else 0))
              = ∑ d ∈ (Pz A z).divisors,
                  (if d ∣ n then (if rdMinus D d then
                    ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.weights n else 0) := by
                refine Finset.sum_congr rfl (fun d _ => ?_)
                by_cases h : d ∣ n <;> simp [h]
            _ = (∑ d ∈ (Pz A z).divisors.filter (fun d => d ∣ n),
                  (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
                    * A.weights n) := by
                rw [Finset.sum_filter]
            _ = (∑ d ∈ (Pz A z).divisors.filter (fun d => d ∣ n),
                  (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
                  * A.weights n :=
                (Finset.sum_mul _ _ _).symm
            _ = (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
                  (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
                  * A.weights n := by
                rw [hset]
            _ = A.weights n * (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
                  (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)) := by ring
        rw [h1]
        have h2 : (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
              (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
            ≤ (if Nat.gcd n (Pz A z) = 1 then 1 else 0) :=
          lamMinus_moebius_sum_le _
            (Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right n (Pz A z)) (Pz_squarefree A z)) D hD
        calc A.weights n * (∑ d ∈ (Nat.gcd n (Pz A z)).divisors,
              (if rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))
            ≤ A.weights n * (if Nat.gcd n (Pz A z) = 1 then 1 else 0) :=
              mul_le_mul_of_nonneg_left h2 (A.weights_nonneg n)
          _ = (if Nat.gcd n (Pz A z) = 1 then 1 else 0) * A.weights n := by ring
    _ = ∑ n ∈ A.support,
          (if ∀ p ∈ A.prodPrimes.primeFactors, (p:ℝ) < z → ¬ p ∣ n then A.weights n else 0) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases h : Nat.gcd n (Pz A z) = 1
        · rw [if_pos h, if_pos ((coprime_Pz_iff A n z).mp h)]; ring
        · rw [if_neg h, if_neg (fun hh => h ((coprime_Pz_iff A n z).mpr hh))]; ring
    _ = siftedSumR A z := by rw [siftedSumR]

end

end Work.ChenPlan.LinearSieve.RI
