/-
  Companion paper, §3, the completion step (3.5)

      `S(x) − S(x;Z) = ∑_{p ≤ Z} log p · a_p`,   `0 ≤ S(x) − S(x;Z) ≪ A(x)(log x)^{−1}`,

  where `S(x) = ∑_{n ≤ x} a_n Λ(n)` is the prime sum and `S(x;Z) = ∑_{n ≤ x} a_n ρ_n Λ(n>Z)`.

  The point is that `Λ(n) ≠ 0` only for prime powers and `a` is squarefree-supported, so the
  `n` contributing to `S(x)` are primes; and primes `p > Z ≥ Δ` have `ρ_p = λ_1 = 1` because
  the sieve weight `λ` is supported on `[1, Δ]`.
-/
import Mathlib
import Submission.ASP.Defs
import Submission.Commons.NumberTheory.ArithmeticFunction.prime_of_squarefree_vonMangoldt_ne_zero

set_option maxHeartbeats 800000

namespace Submission.ASP

open Finset

noncomputable section

/-- `ρ_p = 1` for a prime `p > Δ`, when `λ` is supported on `[1,Δ]` with `λ 1 = 1`. -/
lemma rhoOf_prime_eq_one (lam : ℕ → ℝ) (Δ : ℕ) (hlam1 : lam 1 = 1)
    (hlam_supp : ∀ ν, Δ < ν → lam ν = 0) {p : ℕ} (hp : p.Prime) (hΔp : Δ < p) :
    rhoOf lam p = 1 := by
  rw [rhoOf, hp.divisors,
    Finset.sum_insert (by rw [Finset.mem_singleton]; exact Ne.symm hp.ne_one),
    Finset.sum_singleton, hlam_supp p hΔp, hlam1, add_zero]

/-- **(3.5), the identity**: `S(x) − S(x;Z) = ∑_{p ≤ Z} log p · a_p`. -/
theorem S_sub_SZ_eq (a lam : ℕ → ℝ) (N Z Δ : ℕ)
    (ha_sq : ∀ n, ¬ Squarefree n → a n = 0)
    (hlam1 : lam 1 = 1) (hlam_supp : ∀ ν, Δ < ν → lam ν = 0) (hΔZ : Δ ≤ Z) (hZN : Z ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, a n * (ArithmeticFunction.vonMangoldt n
        - rhoOf lam n * (if Z < n then ArithmeticFunction.vonMangoldt n else 0)))
      = ∑ p ∈ (Finset.Icc 1 Z).filter Nat.Prime, Real.log (p : ℝ) * a p := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 N)
    (p := fun n => n ≤ Z) (fun n => a n * (ArithmeticFunction.vonMangoldt n
      - rhoOf lam n * (if Z < n then ArithmeticFunction.vonMangoldt n else 0)))
  rw [← hsplit]
  have h1 : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≤ Z),
      a n * (ArithmeticFunction.vonMangoldt n
        - rhoOf lam n * (if Z < n then ArithmeticFunction.vonMangoldt n else 0)))
      = ∑ n ∈ Finset.Icc 1 Z, a n * ArithmeticFunction.vonMangoldt n := by
    have hfil : (Finset.Icc 1 N).filter (fun n => n ≤ Z) = Finset.Icc 1 Z := by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hfil]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    rw [if_neg (by omega)]
    ring
  have h2 : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n ≤ Z),
      a n * (ArithmeticFunction.vonMangoldt n
        - rhoOf lam n * (if Z < n then ArithmeticFunction.vonMangoldt n else 0))) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    have hZn : Z < n := by omega
    rw [if_pos hZn]
    by_cases hsf : Squarefree n
    · by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
      · simp [hΛ]
      · have hp : Nat.Prime n :=
          Commons.NumberTheory.ArithmeticFunction.prime_of_squarefree_vonMangoldt_ne_zero
            hsf hΛ
        have hrho : rhoOf lam n = 1 :=
          rhoOf_prime_eq_one lam Δ hlam1 hlam_supp hp (by omega)
        rw [hrho]; ring
    · rw [ha_sq n hsf]; ring
  rw [h1, h2, add_zero]
  -- the `Λ`-sum over `[1,Z]` localises on primes
  have hz : (∑ n ∈ (Finset.Icc 1 Z).filter (fun n => ¬ Nat.Prime n),
      a n * ArithmeticFunction.vonMangoldt n) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [hΛ]
    · have hsf : ¬ Squarefree n := fun hsf =>
        hn.2 (Commons.NumberTheory.ArithmeticFunction.prime_of_squarefree_vonMangoldt_ne_zero
          hsf hΛ)
      rw [ha_sq n hsf]; ring
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 Z) (p := Nat.Prime)
    (fun n => a n * ArithmeticFunction.vonMangoldt n), hz, add_zero]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  rw [ArithmeticFunction.vonMangoldt_apply_prime hn.2]; ring

/-- **(3.5), the bound**: `S(x) − S(x;Z) ≤ log Z · A(Z)`. -/
theorem S_sub_SZ_le (a : ℕ → ℝ) (Z : ℕ) (hZ : 1 ≤ Z) (ha0 : ∀ n, 0 ≤ a n) :
    (∑ p ∈ (Finset.Icc 1 Z).filter Nat.Prime, Real.log (p : ℝ) * a p)
      ≤ Real.log (Z : ℝ) * ∑ n ∈ Finset.Icc 1 Z, a n := by
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun p hp => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i hi _ => ?_)
  · obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1', hpZ'⟩ := Finset.mem_Icc.mp hpI
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1'
    have hpZ : (p : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hpZ'
    have hlog : Real.log (p : ℝ) ≤ Real.log (Z : ℝ) :=
      Real.log_le_log (by linarith) hpZ
    exact mul_le_mul_of_nonneg_right hlog (ha0 p)
  · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hZ)) (ha0 i)

/-- `∑_{n ≤ N} a_n Λ(n) = ∑_{p ≤ N} log p · a_p` for a squarefree-supported sequence. -/
lemma sum_vonMangoldt_eq_primeSum (a : ℕ → ℝ) (N : ℕ)
    (ha_sq : ∀ n, ¬ Squarefree n → a n = 0) :
    (∑ n ∈ Finset.Icc 1 N, a n * ArithmeticFunction.vonMangoldt n)
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * a p := by
  have hz : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
      a n * ArithmeticFunction.vonMangoldt n) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [hΛ]
    · have hsf : ¬ Squarefree n := fun hsf =>
        hn.2 (Commons.NumberTheory.ArithmeticFunction.prime_of_squarefree_vonMangoldt_ne_zero
          hsf hΛ)
      rw [ha_sq n hsf]; ring
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 N) (p := Nat.Prime)
    (fun n => a n * ArithmeticFunction.vonMangoldt n), hz, add_zero]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  rw [ArithmeticFunction.vonMangoldt_apply_prime hn.2]; ring

/-- **Companion §3, (3.5) + Theorem 1**: the bound for the ρ-weighted Λ-sum transfers to the
prime sum, at the cost of the (3.5) error `log Z · A(Z)`. -/
theorem primeSum_bound_of_S_bound (a lam : ℕ → ℝ) (N Z Δ : ℕ) {H E : ℝ}
    (hZ : 1 ≤ Z) (hZN : Z ≤ N) (hΔZ : Δ ≤ Z) (ha_sq : ∀ n, ¬ Squarefree n → a n = 0)
    (ha0 : ∀ n, 0 ≤ a n) (hlam1 : lam 1 = 1) (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hS : |(∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
        * (if Z < n then ArithmeticFunction.vonMangoldt n else 0)) - H * Acount a (N : ℝ)|
      ≤ E) :
    |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * a p)
        - H * Acount a (N : ℝ)|
      ≤ E + Real.log (Z : ℝ) * Acount a (Z : ℝ) := by
  classical
  have h1 := S_sub_SZ_eq a lam N Z Δ ha_sq hlam1 hlam_supp hΔZ hZN
  have h2 := sum_vonMangoldt_eq_primeSum a N ha_sq
  have h3 : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * a p)
      = (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
          * (if Z < n then ArithmeticFunction.vonMangoldt n else 0))
        + ∑ p ∈ (Finset.Icc 1 Z).filter Nat.Prime, Real.log (p : ℝ) * a p := by
    rw [← h2]
    have hsplit : (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
          * (if Z < n then ArithmeticFunction.vonMangoldt n else 0))
        + ∑ n ∈ Finset.Icc 1 N, a n * (ArithmeticFunction.vonMangoldt n
          - rhoOf lam n * (if Z < n then ArithmeticFunction.vonMangoldt n else 0))
        = ∑ n ∈ Finset.Icc 1 N, a n * ArithmeticFunction.vonMangoldt n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [← hsplit, h1]
  rw [h3]
  have hZ0 : (0:ℝ) ≤ ∑ p ∈ (Finset.Icc 1 Z).filter Nat.Prime, Real.log (p : ℝ) * a p :=
    Finset.sum_nonneg fun p hp => by
      rw [Finset.mem_filter] at hp
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_le)) (ha0 p)
  have hbound := S_sub_SZ_le a Z hZ ha0
  have hAcZ : Acount a (Z : ℝ) = ∑ n ∈ Finset.Icc 1 Z, a n := by
    rw [Acount, Nat.floor_natCast]
  have hAcN : Acount a (N : ℝ) = ∑ n ∈ Finset.Icc 1 N, a n := by
    rw [Acount, Nat.floor_natCast]
  calc |(∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
          * (if Z < n then ArithmeticFunction.vonMangoldt n else 0))
        + (∑ p ∈ (Finset.Icc 1 Z).filter Nat.Prime, Real.log (p : ℝ) * a p)
        - H * Acount a (N : ℝ)|
      = |((∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
            * (if Z < n then ArithmeticFunction.vonMangoldt n else 0))
          - H * Acount a (N : ℝ))
          + (∑ p ∈ (Finset.Icc 1 Z).filter Nat.Prime, Real.log (p : ℝ) * a p)| := by
        ring_nf
    _ ≤ |(∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
            * (if Z < n then ArithmeticFunction.vonMangoldt n else 0))
          - H * Acount a (N : ℝ)|
          + |∑ p ∈ (Finset.Icc 1 Z).filter Nat.Prime, Real.log (p : ℝ) * a p| :=
        abs_add_le _ _
    _ ≤ E + Real.log (Z : ℝ) * Acount a (Z : ℝ) := by
        rw [abs_of_nonneg hZ0]
        exact add_le_add hS (by rw [hAcZ]; exact hbound)

end

end Submission.ASP
