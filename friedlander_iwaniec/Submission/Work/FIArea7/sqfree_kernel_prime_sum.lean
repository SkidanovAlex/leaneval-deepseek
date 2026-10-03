import Mathlib
import Submission.Commons.NumberTheory.Sieve.sum_squarefree_mul_le_prod_primes
import Submission.Commons.NumberTheory.Diophantine.mertens_three_mod_four_prod_bound
import Submission.Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log

namespace Work.FIArea7

open Finset
open scoped BigOperators

/-- The multiplicative weight `p ↦ 4/p` for primes `p ≡ 1 (mod 4)` and `0` otherwise, extended
multiplicatively to `ℕ` by `wt4 n = ∏_{p ∣ n} wt4 p`.  On squarefree `n` all of whose prime
factors are `≡ 1 (mod 4)` this is `4 ^ ω(n) / n`; otherwise it vanishes. -/
private noncomputable def wt4 (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, (if p % 4 = 1 then (4 : ℝ) / (p : ℝ) else 0)

private lemma wt4_one : wt4 1 = 1 := by
  simp [wt4, Nat.primeFactors_one]

private lemma wt4_nonneg (n : ℕ) : 0 ≤ wt4 n := by
  unfold wt4
  apply Finset.prod_nonneg
  intro p _
  by_cases h : p % 4 = 1
  · rw [if_pos h]; exact div_nonneg (by norm_num) (Nat.cast_nonneg p)
  · rw [if_neg h]

private lemma wt4_mul {m n : ℕ} (h : Nat.Coprime m n) : wt4 (m * n) = wt4 m * wt4 n := by
  unfold wt4
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]

/-- For squarefree `d`, the arithmetic function `cardFactors` (number of prime factors counted
with multiplicity) agrees with the number of distinct prime factors. -/
private lemma cardFactors_eq_primeFactors_card (d : ℕ) (h : Squarefree d) :
    ArithmeticFunction.cardFactors d = d.primeFactors.card := by
  rw [ArithmeticFunction.cardFactors_apply]
  simp only [Nat.primeFactors, List.toFinset_card_of_nodup h.nodup_primeFactorsList]

/-- On a squarefree `d` all of whose prime factors are `≡ 1 (mod 4)`, the multiplicative weight
`wt4 d` is `4 ^ ω(d) / d`. -/
private lemma wt4_eq_of_cond (d : ℕ) (hsq : Squarefree d)
    (hcond : ∀ p ∈ d.primeFactors, p % 4 = 1) :
    wt4 d = (4 : ℝ) ^ (ArithmeticFunction.cardFactors d) / (d : ℝ) := by
  have h1 : (∏ p ∈ d.primeFactors, (if p % 4 = 1 then (4 : ℝ) / (p : ℝ) else 0))
      = ∏ p ∈ d.primeFactors, (4 : ℝ) / (p : ℝ) :=
    Finset.prod_congr rfl (fun p hp => if_pos (hcond p hp))
  unfold wt4
  rw [h1, Finset.prod_div_distrib, Finset.prod_const]
  rw [show (∏ x ∈ d.primeFactors, (x : ℝ)) = ((∏ x ∈ d.primeFactors, x : ℕ) : ℝ) by
    push_cast; rfl]
  rw [Nat.prod_primeFactors_of_squarefree hsq, cardFactors_eq_primeFactors_card d hsq]

/-- The squarefree kernel sum is dominated by the Euler product over the primes `≡ 1 (mod 4)`. -/
private lemma sum_le_prod (D : ℕ) :
    (Finset.sum ((Finset.range (D + 1)).filter
        (fun d : ℕ => d ≠ 0 ∧ Squarefree d ∧ (∀ p ∈ d.primeFactors, p % 4 = 1)))
        (fun d => ((4 : ℝ) ^ ArithmeticFunction.cardFactors d) / (d : ℝ)))
      ≤ ∏ p ∈ (Nat.primesLE D).filter (fun p => p % 4 = 1), (1 + 4 / (p : ℝ)) := by
  set A := (Finset.range (D + 1)).filter
      (fun d => d ≠ 0 ∧ Squarefree d ∧ (∀ p ∈ d.primeFactors, p % 4 = 1)) with hA
  set B := (Finset.Icc 1 D).filter Squarefree with hB
  have hAB : A ⊆ B := by
    intro d hd
    rw [hA, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hlt, hne, hsq, _⟩ := hd
    rw [hB, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hsq⟩
  have hterm : ∀ d ∈ A,
      ((4 : ℝ) ^ ArithmeticFunction.cardFactors d) / (d : ℝ) = wt4 d := by
    intro d hd
    rw [hA, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨_, _, hsq, hcond⟩ := hd
    exact (wt4_eq_of_cond d hsq hcond).symm
  have hprime : (Finset.Icc 2 D).filter Nat.Prime = Nat.primesLE D := by
    ext p
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨h2, hD⟩, hp⟩; exact ⟨hD, hp⟩
    · rintro ⟨hD, hp⟩; exact ⟨⟨hp.two_le, hD⟩, hp⟩
  calc (Finset.sum A (fun d => ((4 : ℝ) ^ ArithmeticFunction.cardFactors d) / (d : ℝ)))
      = Finset.sum A wt4 := Finset.sum_congr rfl hterm
    _ ≤ Finset.sum B wt4 :=
        Finset.sum_le_sum_of_subset_of_nonneg hAB (fun d _ _ => wt4_nonneg d)
    _ ≤ ∏ p ∈ (Finset.Icc 2 D).filter Nat.Prime, (1 + wt4 p) :=
        Commons.NumberTheory.Sieve.sum_squarefree_mul_le_prod_primes wt4_one wt4_nonneg
          (fun _ _ h => wt4_mul h) D
    _ = ∏ p ∈ (Nat.primesLE D).filter (fun p => p % 4 = 1), (1 + 4 / (p : ℝ)) := by
        rw [hprime]
        have hpt : ∀ p ∈ Nat.primesLE D, (1 + wt4 p)
            = (if p % 4 = 1 then (1 + 4 / (p : ℝ)) else 1) := by
          intro p hp
          have hp' : p.Prime := (Nat.mem_primesLE.mp hp).2
          rw [show wt4 p = (if p % 4 = 1 then (4 : ℝ) / (p : ℝ) else 0) from by
            unfold wt4; rw [hp'.primeFactors]; simp]
          by_cases h : p % 4 = 1 <;> simp [h]
        rw [Finset.prod_congr rfl hpt, Finset.prod_ite]
        simp

private lemma primesLE_eq_primesBelow (n : ℕ) : Nat.primesLE n = Nat.primesBelow (n + 1) := by
  ext p
  rw [Nat.mem_primesLE, Nat.mem_primesBelow]
  constructor <;> intro h <;> exact ⟨by omega, h.2⟩

/-- The prime-reciprocal sum over the class `1 mod 4` is at most `(1/2) log log D` plus a
constant, for `D ≥ 4`.  This is the arithmetic input: the sharp second Mertens theorem for the
full prime-reciprocal sum, together with the asymptotic `Σ_{p ≡ 3 (4), p ≤ z} 1/p = (1/2) log log z
+ O(1)` and the elementary splitting `Σ_{p ≤ z} 1/p = 1/2 + Σ_{p ≡ 1} 1/p + Σ_{p ≡ 3} 1/p`. -/
private lemma S1_bound (Cm K : ℝ) (D : ℕ) (hD : 4 ≤ D)
    (hMert : ∀ (N : ℕ), 3 ≤ N →
      ∑ p ∈ (N + 1).primesBelow, (1 : ℝ) / (p : ℝ) ≤ Cm + Real.log (Real.log (N : ℝ)))
    (hK : ∀ (z : ℕ), 4 ≤ z →
      |(∑ p ∈ z.primesLE with p % 4 = 3, (1 : ℝ) / (p : ℝ))
        - 1 / 2 * Real.log (Real.log (z : ℝ))| ≤ K) :
    (∑ p ∈ (Nat.primesLE D).filter (fun p => p % 4 = 1), (1 : ℝ) / (p : ℝ))
      ≤ (1 / 2) * Real.log (Real.log (D : ℝ)) + (Cm + K) := by
  have hfull : ∑ p ∈ Nat.primesLE D, (1 : ℝ) / (p : ℝ)
      ≤ Cm + Real.log (Real.log (D : ℝ)) := by
    have h := hMert D (by omega)
    rwa [← primesLE_eq_primesBelow D] at h
  have h3 := hK D hD
  have hS3 : (1 / 2) * Real.log (Real.log (D : ℝ)) - K
      ≤ ∑ p ∈ (Nat.primesLE D).filter (fun p => p % 4 = 3), (1 : ℝ) / (p : ℝ) := by
    have := (abs_le.mp h3).1; linarith
  have hsplit := Commons.NumberTheory.Diophantine.sum_all_split D (by omega)
  linarith [hfull, hS3, hsplit]

/-- The Euler product `∏_{p ≡ 1 (4), p ≤ D} (1 + 4/p)` is `≪ (log D)^2 ≪ (log(2+D))^3`. -/
private lemma prod_bound (C1 : ℝ) (D : ℕ) (hD : 4 ≤ D)
    (hS1 : (∑ p ∈ (Nat.primesLE D).filter (fun p => p % 4 = 1), (1 : ℝ) / (p : ℝ))
      ≤ (1 / 2) * Real.log (Real.log (D : ℝ)) + C1) :
    (∏ p ∈ (Nat.primesLE D).filter (fun p => p % 4 = 1), (1 + 4 / (p : ℝ)))
      ≤ Real.exp (4 * C1) * (1 + Real.log (2 + (D : ℝ))) ^ 3 := by
  set P := (Nat.primesLE D).filter (fun p => p % 4 = 1) with hP
  have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 1 < D)
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  have hlogD : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg hD1.le
  have hstep1 : (∏ p ∈ P, (1 + 4 / (p : ℝ))) ≤ Real.exp (∑ p ∈ P, 4 / (p : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro p _
      exact add_nonneg zero_le_one (div_nonneg (by norm_num) (Nat.cast_nonneg p))
    · intro p _
      rw [add_comm]
      exact Real.add_one_le_exp (4 / (p : ℝ))
  have hsum_eq : (∑ p ∈ P, 4 / (p : ℝ)) = 4 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  have hstep2 : Real.exp (∑ p ∈ P, 4 / (p : ℝ))
      ≤ Real.exp (2 * Real.log (Real.log (D : ℝ)) + 4 * C1) := by
    rw [hsum_eq]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hS1 (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have hexp2 : Real.exp (2 * Real.log (Real.log (D : ℝ))) = (Real.log (D : ℝ)) ^ 2 := by
    have h : Real.exp (2 * Real.log (Real.log (D : ℝ)))
        = Real.exp (Real.log (Real.log (D : ℝ))) ^ 2 := by
      simpa using Real.exp_nat_mul (Real.log (Real.log (D : ℝ))) 2
    rw [h, Real.exp_log (Real.log_pos hD1)]
  have hstep3 : Real.exp (2 * Real.log (Real.log (D : ℝ)) + 4 * C1)
      = (Real.log (D : ℝ)) ^ 2 * Real.exp (4 * C1) := by
    rw [Real.exp_add, hexp2]
  have hlog2D : (1 : ℝ) ≤ 1 + Real.log (2 + (D : ℝ)) := by
    have : 0 ≤ Real.log (2 + (D : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hstep4 : (Real.log (D : ℝ)) ^ 2 ≤ (1 + Real.log (2 + (D : ℝ))) ^ 3 := by
    have hle : Real.log (D : ℝ) ≤ 1 + Real.log (2 + (D : ℝ)) := by
      have h2 : Real.log (D : ℝ) ≤ Real.log (2 + (D : ℝ)) := Real.log_le_log hDpos (by linarith)
      have h3 : 0 ≤ Real.log (2 + (D : ℝ)) := Real.log_nonneg (by linarith)
      linarith
    calc (Real.log (D : ℝ)) ^ 2 ≤ (1 + Real.log (2 + (D : ℝ))) ^ 2 :=
          pow_le_pow_left₀ hlogD hle 2
      _ ≤ (1 + Real.log (2 + (D : ℝ))) ^ 3 :=
          pow_le_pow_right₀ hlog2D (by norm_num)
  calc (∏ p ∈ P, (1 + 4 / (p : ℝ)))
      ≤ Real.exp (∑ p ∈ P, 4 / (p : ℝ)) := hstep1
    _ ≤ Real.exp (2 * Real.log (Real.log (D : ℝ)) + 4 * C1) := hstep2
    _ = (Real.log (D : ℝ)) ^ 2 * Real.exp (4 * C1) := hstep3
    _ ≤ (1 + Real.log (2 + (D : ℝ))) ^ 3 * Real.exp (4 * C1) :=
        mul_le_mul_of_nonneg_right hstep4 (Real.exp_pos _).le
    _ = Real.exp (4 * C1) * (1 + Real.log (2 + (D : ℝ))) ^ 3 := by ring

/-- For `D ≤ 3` the set of primes `≡ 1 (mod 4)` up to `D` is empty, so the Euler product is `1`. -/
private lemma prod_eq_one_of_le_three (D : ℕ) (hD : D ≤ 3) :
    (∏ p ∈ (Nat.primesLE D).filter (fun p => p % 4 = 1), (1 + 4 / (p : ℝ))) = 1 := by
  have hempty : (Nat.primesLE D).filter (fun p => p % 4 = 1) = ∅ := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hmod⟩ := hp
      rw [Nat.mem_primesLE] at hp1
      obtain ⟨hle, hprime⟩ := hp1
      have h2 := hprime.two_le
      have hple3 : p ≤ 3 := le_trans hle hD
      interval_cases p <;> norm_num at hmod
    · intro hp; simp at hp
  rw [hempty, Finset.prod_empty]

theorem sqfree_kernel_prime_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ,
      (Finset.sum ((Finset.range (D + 1)).filter
        (fun d : ℕ => d ≠ 0 ∧ Squarefree d ∧ (∀ p ∈ d.primeFactors, p % 4 = 1)))
        (fun d => ((4 : ℝ) ^ ArithmeticFunction.cardFactors d) / (d : ℝ)))
      ≤ C * (1 + Real.log (2 + (D : ℝ))) ^ 3 := by
  obtain ⟨Cm, _hCmnn, hMert⟩ := Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log
  obtain ⟨K, _hKpos, hK⟩ := Commons.NumberTheory.Diophantine.sum_three_mod_four_bound_all
  refine ⟨max 1 (Real.exp (4 * (Cm + K))), ?_, fun D => ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · have hSD := sum_le_prod D
    by_cases hD : D ≤ 3
    · rw [prod_eq_one_of_le_three D hD] at hSD
      have hCge1 : (1 : ℝ) ≤ max 1 (Real.exp (4 * (Cm + K))) := le_max_left _ _
      have hbase : (1 : ℝ) ≤ (1 + Real.log (2 + (D : ℝ))) ^ 3 := by
        have h0 : (0 : ℝ) ≤ Real.log (2 + (D : ℝ)) :=
          Real.log_nonneg (by have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D; linarith)
        have h1 : (1 : ℝ) ≤ 1 + Real.log (2 + (D : ℝ)) := by linarith
        have h2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) h1 3
        simpa using h2
      refine le_trans hSD ?_
      have h := mul_le_mul hCge1 hbase (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ max 1 (Real.exp (4 * (Cm + K))))
      simpa using h
    · have hD4 : 4 ≤ D := by omega
      have hS1 := S1_bound Cm K D hD4 hMert hK
      have hprod := prod_bound (Cm + K) D hD4 hS1
      have hle : Real.exp (4 * (Cm + K)) ≤ max 1 (Real.exp (4 * (Cm + K))) :=
        le_max_right _ _
      calc (Finset.sum ((Finset.range (D + 1)).filter
              (fun d : ℕ => d ≠ 0 ∧ Squarefree d ∧ (∀ p ∈ d.primeFactors, p % 4 = 1)))
              (fun d => ((4 : ℝ) ^ ArithmeticFunction.cardFactors d) / (d : ℝ)))
          ≤ ∏ p ∈ (Nat.primesLE D).filter (fun p => p % 4 = 1), (1 + 4 / (p : ℝ)) := hSD
        _ ≤ Real.exp (4 * (Cm + K)) * (1 + Real.log (2 + (D : ℝ))) ^ 3 := hprod
        _ ≤ max 1 (Real.exp (4 * (Cm + K))) * (1 + Real.log (2 + (D : ℝ))) ^ 3 := by
            apply mul_le_mul_of_nonneg_right hle
            have h0 : (0 : ℝ) ≤ Real.log (2 + (D : ℝ)) :=
              Real.log_nonneg (by have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D; linarith)
            exact pow_nonneg (by linarith) 3

end Work.FIArea7
