import Mathlib
import Submission.Chen.SwitchDefs
import Submission.ChenPlan.Interfaces

/-!
# Chen's `h1`: the sieve problem

The sieve problem of Chen's `h1` at the sift limit `M` (`Submission.chenSiftLimitTenth x`
at the end):

* support: the shifted primes `n = p + 2` with `p ≤ x` prime,
* weights: `log (n - 2) = log p`,
* sifting primes: the odd primes below `M` (`ChenEight.oddPrimLt M`),
* `X = totalMass = x`, density `ν d = 1/φ(d)`.

This module builds the `BoundingSieve` instance and identifies its `siftedSum`, `sieveV`,
`rem` and `remSum` with the objects of the `h1` statement (`goodSum`, `VsieveOdd`, `rD`).
-/

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.ChenPlan.H1

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight

/-! ## The arithmetic function `d ↦ 1/φ(d)` -/

/-- `d ↦ 1/φ(d)` as an arithmetic function; multiplicative, with value `1/(p-1)` at an odd prime. -/
def invTotient : ArithmeticFunction ℝ :=
  ⟨fun n => ((Nat.totient n : ℕ) : ℝ)⁻¹, by simp⟩

lemma invTotient_apply (n : ℕ) : invTotient n = ((Nat.totient n : ℕ) : ℝ)⁻¹ := rfl

lemma invTotient_mult : ArithmeticFunction.IsMultiplicative invTotient := by
  constructor
  · rw [invTotient_apply, Nat.totient_one]; norm_num
  · intro m n hmn
    rw [invTotient_apply, invTotient_apply, invTotient_apply, Nat.totient_mul hmn,
      Nat.cast_mul, mul_inv]

/-! ## The support, the weights, and the sieve -/

/-- The support of the sieve: the shifted primes `p + 2`, `p ≤ x` prime. -/
def chenSupport (x : ℕ) : Finset ℕ :=
  ((Finset.range (x + 1)).filter (fun p : ℕ => p.Prime)).image (fun p => p + 2)

/-- The weight of the shifted prime `n = p + 2`: `log (n - 2) = log p`. -/
def chenWeight (n : ℕ) : ℝ := Real.log (((n - 2 : ℕ)) : ℝ)

lemma chenWeight_nonneg (n : ℕ) : 0 ≤ chenWeight n := by
  rcases Nat.eq_zero_or_pos (n - 2) with h | h
  · simp [chenWeight, h]
  · exact Real.log_nonneg (by exact_mod_cast h)

lemma chenWeight_add_two (p : ℕ) : chenWeight (p + 2) = Real.log (p : ℝ) := by
  simp [chenWeight]

/-- The odd primorial below `M` is squarefree. -/
lemma oddPrimLt_squarefree (M : ℕ) : Squarefree (oddPrimLt M) := by
  rw [oddPrimLt_eq_prod_oddLt, Nat.squarefree_iff_prime_squarefree]
  intro p hp hpsq
  have hpdvd : p ∣ ∏ q ∈ oddLt M, q := dvd_trans (dvd_mul_right p p) hpsq
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q : ℕ => q)).mp hpdvd
  have hqprime : q.Prime := (Submission.mem_oddLt.mp hq).1
  have hpq_eq : p = q := by
    rcases (Nat.dvd_prime hqprime).mp hpq with h | h
    · exact absurd h hp.ne_one
    · exact h
  subst hpq_eq
  have hmem : p ∈ oddLt M := hq
  rw [← Finset.mul_prod_erase (oddLt M) (fun x : ℕ => x) hmem] at hpsq
  rw [Nat.mul_dvd_mul_iff_left hp.pos] at hpsq
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun x : ℕ => x)).mp hpsq
  have hrprime : r.Prime := (Submission.mem_oddLt.mp (Finset.mem_of_mem_erase hr)).1
  have hpr_eq : p = r := by
    rcases (Nat.dvd_prime hrprime).mp hpr with h | h
    · exact absurd h hp.ne_one
    · exact h
  have hmem' : r ∈ (oddLt M).erase p := hr
  rw [← hpr_eq] at hmem'
  exact Finset.notMem_erase p (oddLt M) hmem'

/-- **Chen's sieve problem** for the shifted primes: weights `log p` on `{p + 2 : p ≤ x}`, sifting
the odd primes below `M`, approximation `X = x`, density `ν d = 1/φ(d)`. -/
def chenSieve (x M : ℕ) : BoundingSieve where
  support := chenSupport x
  prodPrimes := oddPrimLt M
  prodPrimes_squarefree := oddPrimLt_squarefree M
  weights := chenWeight
  weights_nonneg := chenWeight_nonneg
  totalMass := x
  nu := invTotient
  nu_mult := invTotient_mult
  nu_pos_of_prime := by
    intro p hp _
    rw [invTotient_apply]
    exact inv_pos.mpr (by exact_mod_cast (Nat.totient_pos.mpr hp.pos))
  nu_lt_one_of_prime := by
    intro p hp hpd
    rw [invTotient_apply]
    have hpne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpd
      have h0 : oddPrimLt M % 2 = 0 := Nat.mod_eq_zero_of_dvd hpd
      have h1 := oddPrimLt_odd M
      omega
    have hp3 : 3 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hpne2
      · omega
    rw [Nat.totient_prime hp, Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    exact inv_lt_one_of_one_lt₀ (by linarith)

/-! ## The identification of the sieve quantities -/

/-- The weight of the multiples of `d` in the sieve is `θ_d(x)`. -/
lemma chenSieve_multSum (x M d : ℕ) : (chenSieve x M).multSum d = thetaD x d := by
  rw [BoundingSieve.multSum]
  rw [show (chenSieve x M).support = chenSupport x from rfl,
    show (chenSieve x M).weights = chenWeight from rfl]
  rw [chenSupport, Finset.sum_image]
  · rw [thetaD_eq]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    by_cases h : d ∣ p + 2
    · simp [h, chenWeight_add_two p]
    · simp [h]
  · intro a _ b _ hab
    exact Nat.add_right_cancel hab

/-- The remainder of the sieve is `r_d = θ_d(x) - x/φ(d)`. -/
lemma chenSieve_rem (x M d : ℕ) : (chenSieve x M).rem d = rD x d := by
  rw [BoundingSieve.rem, chenSieve_multSum]
  rw [show (chenSieve x M).nu d = invTotient d from rfl,
    show (chenSieve x M).totalMass = (x : ℝ) from rfl, invTotient_apply, rD]
  rw [div_eq_inv_mul]

/-- The sifted sum of the sieve is Chen's `goodSum`. -/
lemma chenSieve_siftedSum (x M : ℕ) : (chenSieve x M).siftedSum = goodSum x M := by
  rw [BoundingSieve.siftedSum]
  rw [show (chenSieve x M).support = chenSupport x from rfl,
    show (chenSieve x M).prodPrimes = oddPrimLt M from rfl,
    show (chenSieve x M).weights = chenWeight from rfl]
  rw [chenSupport, Finset.sum_image]
  · simp only [goodSum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [chenWeight_add_two p]
    simp only [Commons.NumberTheory.Chen.ChenEight.Id]
    by_cases h : (oddPrimLt M).Coprime (p + 2)
    · rw [if_pos h, if_pos (Nat.Coprime.symm h), mul_one]
    · rw [if_neg h, if_neg (fun hc => h (Nat.Coprime.symm hc)), mul_zero]
  · intro a _ b _ hab
    exact Nat.add_right_cancel hab

/-- `sieveV` of the sieve is the odd Euler product `VsieveOdd`. -/
lemma chenSieve_sieveV (x M : ℕ) : Submission.ChenPlan.sieveV (chenSieve x M) = VsieveOdd M := by
  rw [Submission.ChenPlan.sieveV]
  rw [show (chenSieve x M).prodPrimes = oddPrimLt M from rfl,
    show (chenSieve x M).nu = invTotient from rfl]
  have hpf : (oddPrimLt M).primeFactors = oddLt M := by
    rw [oddPrimLt_eq_prod_oddLt]
    exact Nat.primeFactors_prod (fun p hp => (Submission.mem_oddLt.mp hp).1)
  rw [hpf]
  unfold VsieveOdd
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp3 : 3 ≤ p := (Submission.mem_oddLt.mp hp).2.1
  rw [invTotient_apply, Nat.totient_prime (Submission.mem_oddLt.mp hp).1, Nat.cast_sub (by omega : 1 ≤ p)]
  push_cast
  ring

/-- `remSum` of the sieve is the `3^{ω(d)}`-weighted sum of `|r_d|` over the divisors of the
odd primorial below `D`. -/
lemma chenSieve_remSum (x M : ℕ) (D : ℝ) :
    Submission.ChenPlan.remSum (chenSieve x M) D
      = ∑ d ∈ (oddPrimLt M).divisors.filter (fun d : ℕ => (d : ℝ) < D),
          (3 : ℝ) ^ d.primeFactors.card * |rD x d| := by
  rw [Submission.ChenPlan.remSum]
  rw [show (chenSieve x M).prodPrimes = oddPrimLt M from rfl]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [chenSieve_rem]

end

end Work.ChenPlan.H1
