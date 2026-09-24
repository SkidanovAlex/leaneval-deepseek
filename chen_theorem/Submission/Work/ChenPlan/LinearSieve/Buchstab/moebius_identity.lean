import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic

/-!
# The Möbius (exact) identity for the sifted sum

For a `BoundingSieve` `s` with `P = s.prodPrimes`, `ν = s.nu`, the sifted sum is exactly

  `S(A, z) = X · V + Σ_{d ∣ P} μ(d) r_d`,  where `V = ∏_{p ∣ P} (1 - ν(p))`, `X = s.totalMass`,
  `r_d = s.multSum d - ν(d) X`.

This is Möbius inversion on the divisors of `P`:
`Σ_{d ∣ P} μ(d) [d ∣ n] = [gcd(n, P) = 1]`, together with the multiplicativity
`Σ_{d ∣ P} μ(d) ν(d) = ∏_{p ∣ P} (1 - ν(p))` (Mathlib's
`IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree`).

This is the `e = 1` (parity-exact, no iteration) member of the Buchstab family and the seed of the
Jurkat–Richert development: every `Λ²`/Buchstab bound is this identity plus a remainder estimate.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Work.ChenPlan.LinearSieve.Buchstab

/-- `Σ_{d ∣ n} μ(d) = [n = 1]`, in `ℝ`. -/
theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = if n = 1 then 1 else 0 := by
  have key : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ζ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have h := DFunLike.congr_fun key n
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [ArithmeticFunction.one_apply] at h
  exact h

/-- **Möbius inversion of the sifted sum**: `Σ_{d ∣ P} μ(d) · multSum d = S(A, z)`. -/
theorem sum_mu_multSum_eq_siftedSum (s : BoundingSieve) :
    (∑ d ∈ s.prodPrimes.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * s.multSum d)
      = s.siftedSum := by
  rw [BoundingSieve.siftedSum_eq_sum_support_mul_ite]
  simp only [BoundingSieve.multSum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hdvd : s.prodPrimes.divisors.filter (fun d => d ∣ n)
      = (s.prodPrimes.gcd n).divisors := by
    rw [← Nat.divisors_filter_dvd_of_dvd (BoundingSieve.prodPrimes_ne_zero (s := s))
      (Nat.gcd_dvd_left _ _)]
    apply Finset.filter_congr
    intro d hd
    rw [Nat.dvd_gcd_iff]
    constructor
    · intro h; exact ⟨Nat.dvd_of_mem_divisors hd, h⟩
    · intro h; exact h.2
  rw [show (∑ x ∈ s.prodPrimes.divisors,
        ((ArithmeticFunction.moebius x : ℤ) : ℝ) * (if x ∣ n then s.weights n else 0))
      = (∑ x ∈ s.prodPrimes.divisors.filter (fun x => x ∣ n),
        ((ArithmeticFunction.moebius x : ℤ) : ℝ)) * s.weights n by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter, ← Finset.sum_mul]]
  rw [hdvd, sum_moebius_divisors]
  ring

/-- `V = Σ_{d ∣ P} μ(d) ν(d)`: the main-term factor is the Möbius transform of `ν`. -/
theorem sieveV_eq_sum_mu_nu (s : BoundingSieve) :
    Submission.ChenPlan.sieveV s
      = ∑ d ∈ s.prodPrimes.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * s.nu d := by
  rw [Submission.ChenPlan.sieveV,
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree s.nu s.nu_mult
      s.prodPrimes_squarefree]

/-- **The Möbius identity** (exact form of `S(A,z) = X V + Σ μ(d) r_d`). -/
theorem moebius_identity (s : BoundingSieve) :
    s.siftedSum = s.totalMass * Submission.ChenPlan.sieveV s
      + Work.ChenPlan.LinearSieve.moebiusRemSum s := by
  rw [← sum_mu_multSum_eq_siftedSum s, Work.ChenPlan.LinearSieve.moebiusRemSum, sieveV_eq_sum_mu_nu]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [BoundingSieve.multSum_eq_main_err]
  ring

end Work.ChenPlan.LinearSieve.Buchstab
