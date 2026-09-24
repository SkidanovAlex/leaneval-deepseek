import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.CorrectionDefs
import Submission.Work.NumberTheory.Chen.BTermCount.Bounds
import Submission.Commons.NumberTheory.Tenenbaum.multiplicative_average_bound

open Finset Filter
open scoped BigOperators Topology

open Commons.NumberTheory.Chen.ChenEight

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The level of distribution for the "shared mass" `bShared`

This file proves

`Work.NumberTheory.Chen.BTermCount.bSharedLevelOfDistribution`

the elementary (systematic) part of the bilinear level of distribution for the ternary sieve
sequence, see `CorrectionDefs.lean`.  The quantity

`bShared x M Y d = #{n ∈ B̄ : ∃ p prime, p ∣ d ∧ p ∣ n}`

counts the elements of `B̄ = bProdSet x M Y` sharing a prime factor with `d`.  Since every
prime factor of every element of `B̄` is at least `M = chenSiftLimit x ≈ x^{1/14}` (eventually)
and every element of `B̄` is at most `x + 2`, we get

`bShared x M Y d ≤ Σ_{p ∣ d} #{n ∈ B̄ : p ∣ n} ≤ Σ_{p ∣ d} (x+2)/p`,

and summing over the odd `d ≤ D` with the sieve weights `3 ^ (ω d) / φ d` produces the
elementary main term `O(x^{13/14} (log x)^6) = o(x / (log x)^A)`, which is exactly the target.

The mean value input is the recursion

`∑_{m ≤ N} k ^ (ω m) / m ≤ (log N + 1) · ∑_{m ≤ N} (k-1) ^ (ω m) / m`

obtained from the expansion `k ^ (ω m) = ∑_{d ∣ m, squarefree} (k-1) ^ (ω d)`.
-/

/-! ## 1. The mean value of `k ^ ω` -/

/-- `Fk k D = ∑_{m ∈ [1,D]} k ^ (ω m) / m`. -/
noncomputable def Fk (k D : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 D, ((k : ℝ) ^ (m.primeFactors.card)) / (m : ℝ)

/-- Expansion of `∏_{p ∣ m} (1 + g p)` as a sum over squarefree divisors of `m`. -/
lemma prod_one_add_eq_sum_sqfree_divisors (g : ℕ → ℝ) (m : ℕ) (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, (1 + g p)
      = ∑ d ∈ m.divisors.filter Squarefree, ∏ p ∈ d.primeFactors, g p := by
  rw [Finset.prod_one_add]
  exact (Commons.NumberTheory.Nat.sum_squarefree_divisors_eq_sum_powerset_primeFactors m hm g).symm

/-- `k ^ (ω m)` as a sum over the squarefree divisors of `m`. -/
lemma pow_card_eq_sum_sqfree_divisors (k m : ℕ) (hk : 1 ≤ k) (hm : m ≠ 0) :
    (k : ℝ) ^ (m.primeFactors.card)
      = ∑ d ∈ m.divisors.filter Squarefree, ((k : ℝ) - 1) ^ (d.primeFactors.card) := by
  have h := prod_one_add_eq_sum_sqfree_divisors (fun _ : ℕ => (k : ℝ) - 1) m hm
  have h1 : (∏ p ∈ m.primeFactors, (1 + ((k : ℝ) - 1))) = (k : ℝ) ^ (m.primeFactors.card) := by
    rw [Finset.prod_const]
    congr 1
    ring
  rw [h1] at h
  rw [h]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.prod_const]

/-- Injecting `m ↦ m / d` into `[1, D]` bounds a sum over the multiples of `d`. -/
lemma sum_div_comp_le (d D : ℕ) (hd : 1 ≤ d) (f : ℕ → ℝ)
    (hf : ∀ j ∈ Finset.Icc 1 D, 0 ≤ f j) :
    (∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m), f (m / d))
      ≤ ∑ j ∈ Finset.Icc 1 D, f j := by
  have hinj : Set.InjOn (fun m : ℕ => m / d)
      ↑((Finset.Icc 1 D).filter (fun m => d ∣ m)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have hab' : a / d = b / d := hab
    have ha' : a = d * (a / d) := (Nat.mul_div_cancel' ha.2).symm
    have hb' : b = d * (b / d) := (Nat.mul_div_cancel' hb.2).symm
    rw [ha', hb', hab']
  have hsub : ((Finset.Icc 1 D).filter (fun m => d ∣ m)).image (fun m => m / d)
      ⊆ Finset.Icc 1 D := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨m, hm, rfl⟩ := hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    have hdvd : d ∣ m := hm.2
    have hm_eq : m = d * (m / d) := (Nat.mul_div_cancel' hdvd).symm
    have hk : 1 ≤ m / d := by
      rcases Nat.eq_zero_or_pos (m / d) with h | h
      · rw [h, mul_zero] at hm_eq
        omega
      · exact h
    exact Finset.mem_Icc.mpr ⟨hk, le_trans (Nat.div_le_self m d) hm.1.2⟩
  calc (∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m), f (m / d))
      = ∑ y ∈ ((Finset.Icc 1 D).filter (fun m => d ∣ m)).image (fun m => m / d), f y :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 D, f j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hf j hj)

/-- Reindexing a double sum over `d ∣ m` by exchanging the order. -/
lemma sum_divisors_swap (F : ℕ → ℕ → ℝ) (D : ℕ) :
    (∑ m ∈ Finset.Icc 1 D, ∑ d ∈ m.divisors, F m d)
      = ∑ d ∈ Finset.Icc 1 D,
          ∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m), F m d := by
  have h1 : ∀ m ∈ Finset.Icc 1 D, (∑ d ∈ m.divisors, F m d)
      = ∑ d ∈ Finset.Icc 1 D, (if d ∣ m then F m d else 0) := by
    intro m hm
    rw [Commons.NumberTheory.Tenenbaum.divisors_eq_Icc_filter_dvd D m
      (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.sum_filter]

/-- The bound on a sum over multiples of `d` of `1 / m`. -/
lemma sum_inv_div_comp_le (d D : ℕ) (hd : 1 ≤ d) :
    (∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m), (1:ℝ)/(m:ℝ))
      ≤ (1/(d:ℝ)) * (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ)) := by
  have hcast : ∀ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
      (1:ℝ)/(m:ℝ) = (1/(d:ℝ)) * (1/(((m / d : ℕ)) : ℝ)) := by
    intro m hm
    obtain ⟨hmI, hdm⟩ := Finset.mem_filter.mp hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
    have hm0 : m ≠ 0 := by omega
    have hdiv0 : m / d ≠ 0 := by
      rintro h
      have h' := Nat.mul_div_cancel' hdm
      rw [h, mul_zero] at h'
      omega
    have hmcast : (m:ℝ) = (d:ℝ) * (((m / d : ℕ)) : ℝ) := by
      have hmd : d * (m / d) = m := Nat.mul_div_cancel' hdm
      conv_lhs => rw [← hmd]
      push_cast
      ring
    rw [hmcast]
    have hd0 : (d:ℝ) ≠ 0 := by
      have : (0:ℝ) < (d:ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hd)
      exact ne_of_gt this
    have hq0 : (((m / d : ℕ)) : ℝ) ≠ 0 := by
      have : (0:ℝ) < (((m / d : ℕ)) : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hdiv0)
      exact ne_of_gt this
    field_simp
  have hcongr : (∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m), (1:ℝ)/(m:ℝ))
      = ∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
          (1/(d:ℝ)) * (1/(((m / d : ℕ)) : ℝ)) := Finset.sum_congr rfl hcast
  have h2 : (∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
        (1/(d:ℝ)) * (1/(((m / d : ℕ)) : ℝ)))
      = (1/(d:ℝ)) * (∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m), (1/(((m / d : ℕ)) : ℝ))) :=
    (Finset.mul_sum _ _ _).symm
  rw [hcongr, h2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact sum_div_comp_le d D hd (fun j => (1:ℝ)/(j:ℝ)) (fun j hj => by positivity)

/-- The sum `∑_{j ≤ D} 1/j` is the `D`-th harmonic number. -/
lemma sum_inv_Icc_eq_harmonic (D : ℕ) :
    (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ)) = ((harmonic D : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [one_div]

lemma one_add_log_nonneg (D : ℕ) : (0:ℝ) ≤ Real.log D + 1 := by
  rcases Nat.eq_zero_or_pos D with h | h
  · subst h
    simp
  · have h1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast h
    have := Real.log_nonneg h1
    linarith

/-- The recursion `Fk k D ≤ (log D + 1) * Fk (k-1) D`. -/
lemma Fk_le_mul (k D : ℕ) (hk : 1 ≤ k) :
    Fk k D ≤ (Real.log D + 1) * Fk (k - 1) D := by
  have step1 : Fk k D = ∑ m ∈ Finset.Icc 1 D,
      ∑ d ∈ m.divisors.filter Squarefree,
        ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ) := by
    unfold Fk
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    rw [pow_card_eq_sum_sqfree_divisors k m hk hm0, Finset.sum_div]
  rw [step1]
  have step2 : ∀ m ∈ Finset.Icc 1 D,
      (∑ d ∈ m.divisors.filter Squarefree, ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ))
        = ∑ d ∈ m.divisors,
            (if Squarefree d then ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ) else 0) := by
    intro m hm
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl step2,
    sum_divisors_swap
      (fun m d => if Squarefree d then ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ) else 0) D]
  have step3 : (∑ d ∈ Finset.Icc 1 D,
        ∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
          (if Squarefree d then ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ) else 0))
      = ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
            ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro d hd
    by_cases hS : Squarefree d
    · rw [if_pos hS]
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [if_pos hS]
    · rw [if_neg hS]
      exact Finset.sum_eq_zero (fun m hm => by rw [if_neg hS])
  rw [step3]
  have hA : ∀ d : ℕ, (0:ℝ) ≤ ((k : ℝ) - 1) ^ (d.primeFactors.card) := by
    intro d
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    exact pow_nonneg (by linarith) _
  have hstep4 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
          ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ))
      ≤ (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((k : ℝ) - 1) ^ (d.primeFactors.card) * ((1:ℝ)/(d:ℝ))) *
            (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ)) := by
    have hinner : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
            ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ))
        ≤ ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((k : ℝ) - 1) ^ (d.primeFactors.card) * ((1:ℝ)/(d:ℝ)) *
              (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      calc (∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
              ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ))
          = ((k : ℝ) - 1) ^ (d.primeFactors.card) *
              (∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m), (1:ℝ)/(m:ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro m hm
            ring
        _ ≤ ((k : ℝ) - 1) ^ (d.primeFactors.card) *
              ((1/(d:ℝ)) * (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ))) :=
            mul_le_mul_of_nonneg_left (sum_inv_div_comp_le d D hd1) (hA d)
        _ = ((k : ℝ) - 1) ^ (d.primeFactors.card) * ((1:ℝ)/(d:ℝ)) *
              (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ)) := by ring
    refine le_trans hinner ?_
    rw [Finset.sum_mul]
  have hstep6 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((k : ℝ) - 1) ^ (d.primeFactors.card) * ((1:ℝ)/(d:ℝ)))
      ≤ Fk (k - 1) D := by
    have h1 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((k : ℝ) - 1) ^ (d.primeFactors.card) * ((1:ℝ)/(d:ℝ)))
        = ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((k : ℝ) - 1) ^ (d.primeFactors.card) / (d:ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [mul_one_div]
    rw [h1]
    have h2 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((k : ℝ) - 1) ^ (d.primeFactors.card) / (d:ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 D, ((k : ℝ) - 1) ^ (d.primeFactors.card) / (d:ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro d hd hnot
      exact div_nonneg (hA d) (by positivity)
    refine le_trans h2 (le_of_eq ?_)
    have hcast1 : ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk]
      norm_num
    unfold Fk
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [hcast1]
  have hstep7 : (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ)) ≤ Real.log D + 1 := by
    rw [sum_inv_Icc_eq_harmonic]
    linarith [harmonic_le_one_add_log D]
  have hHnn : (0:ℝ) ≤ ∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ) := by positivity
  have hFknn : (0:ℝ) ≤ Fk (k - 1) D := by
    unfold Fk
    positivity
  calc (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ∑ m ∈ (Finset.Icc 1 D).filter (fun m => d ∣ m),
          ((k : ℝ) - 1) ^ (d.primeFactors.card) / (m : ℝ))
      ≤ (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((k : ℝ) - 1) ^ (d.primeFactors.card) * ((1:ℝ)/(d:ℝ))) *
            (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ)) := hstep4
    _ ≤ Fk (k - 1) D * (∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ)) :=
        mul_le_mul_of_nonneg_right hstep6 hHnn
    _ ≤ Fk (k - 1) D * (Real.log D + 1) := mul_le_mul_of_nonneg_left hstep7 hFknn
    _ = (Real.log D + 1) * Fk (k - 1) D := by ring

/-- The base case `k = 1`. -/
lemma Fk_one_le (D : ℕ) : Fk 1 D ≤ Real.log D + 1 := by
  have h1 : Fk 1 D = ∑ j ∈ Finset.Icc 1 D, (1:ℝ)/(j:ℝ) := by
    unfold Fk
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp
  rw [h1, sum_inv_Icc_eq_harmonic]
  linarith [harmonic_le_one_add_log D]

/-- `Fk k D ≤ (log D + 1)^k`. -/
lemma Fk_le_pow (k D : ℕ) (hk : 1 ≤ k) : Fk k D ≤ (Real.log D + 1) ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simpa using Fk_one_le D
      · have ih' := ih hkpos
        calc Fk (k + 1) D ≤ (Real.log D + 1) * Fk k D := Fk_le_mul (k + 1) D (by omega)
          _ ≤ (Real.log D + 1) * (Real.log D + 1) ^ k :=
              mul_le_mul_of_nonneg_left ih' (one_add_log_nonneg D)
          _ = (Real.log D + 1) ^ (k + 1) := by rw [pow_succ]; ring

/-! ## 2. The totient lower bound -/

/-- `m ≤ φ m * 2 ^ (ω m)`. -/
lemma le_totient_mul_two_pow_card (m : ℕ) : m ≤ m.totient * 2 ^ (m.primeFactors.card) := by
  have hP : 0 < ∏ p ∈ m.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hR : (∏ p ∈ m.primeFactors, p)
      ≤ (∏ p ∈ m.primeFactors, (p - 1)) * 2 ^ (m.primeFactors.card) := by
    calc (∏ p ∈ m.primeFactors, p)
        ≤ ∏ p ∈ m.primeFactors, ((p - 1) * 2) := by
          refine Finset.prod_le_prod₀ (fun p hp => by positivity) ?_
          intro p hp
          have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
          omega
      _ = (∏ p ∈ m.primeFactors, (p - 1)) * (∏ p ∈ m.primeFactors, 2) :=
          Finset.prod_mul_distrib
      _ = (∏ p ∈ m.primeFactors, (p - 1)) * 2 ^ (m.primeFactors.card) := by
          rw [Finset.prod_const]
  have h1 : m.totient * (∏ p ∈ m.primeFactors, p) = m * ∏ p ∈ m.primeFactors, (p - 1) :=
    Nat.totient_mul_prod_primeFactors m
  have h2 : m * (∏ p ∈ m.primeFactors, (p - 1))
      ≤ (m.totient * 2 ^ (m.primeFactors.card)) * (∏ p ∈ m.primeFactors, (p - 1)) := by
    calc m * (∏ p ∈ m.primeFactors, (p - 1))
        = m.totient * (∏ p ∈ m.primeFactors, p) := h1.symm
      _ ≤ m.totient * ((∏ p ∈ m.primeFactors, (p - 1)) * 2 ^ (m.primeFactors.card)) :=
          Nat.mul_le_mul_left _ hR
      _ = (m.totient * 2 ^ (m.primeFactors.card)) * (∏ p ∈ m.primeFactors, (p - 1)) := by ring
  exact Nat.le_of_mul_le_mul_right h2 hP

/-- `∑_{m ≤ D} 3 ^ (ω m) / φ m ≤ Fk 6 D`. -/
lemma sum_pow_three_div_totient_le_six (D : ℕ) :
    (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) ≤ Fk 6 D := by
  unfold Fk
  refine Finset.sum_le_sum ?_
  intro m hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hφpos : (0:ℝ) < (m.totient:ℝ) := by
    have : 0 < m.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  have hkey : (m:ℝ) ≤ (m.totient:ℝ) * 2 ^ (m.primeFactors.card) := by
    have := le_totient_mul_two_pow_card m
    exact_mod_cast this
  rw [div_le_div_iff₀ hφpos hmpos]
  calc (3:ℝ) ^ (m.primeFactors.card) * (m:ℝ)
      ≤ (3:ℝ) ^ (m.primeFactors.card) * ((m.totient:ℝ) * 2 ^ (m.primeFactors.card)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (3:ℝ) ^ (m.primeFactors.card) * (2:ℝ) ^ (m.primeFactors.card) * (m.totient:ℝ) := by ring
    _ = (6:ℝ) ^ (m.primeFactors.card) * (m.totient:ℝ) := by
        rw [← mul_pow]
        norm_num

/-- `∑_{m ≤ D} 3 ^ (ω m) / φ m ≤ (log D + 1)^6`. -/
lemma sum_pow_three_div_totient_le (D : ℕ) :
    (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ))
      ≤ (Real.log D + 1) ^ 6 :=
  le_trans (sum_pow_three_div_totient_le_six D) (Fk_le_pow 6 D (by norm_num))

/-! ## 3. Elementary bounds for the "shared mass" -/

/-- `bShared x M Y d` is at most the sum, over the prime divisors `p` of `d`, of the number of
elements of `B̄` divisible by `p`. -/
lemma bShared_le_sum_primeFactors (x M Y d : ℕ) (hd : 0 < d) :
    bShared x M Y d
      ≤ ∑ p ∈ d.primeFactors, ((bProdSet x M Y).filter (fun n => p ∣ n)).card := by
  unfold bShared
  have hsub : ((bProdSet x M Y).filter (fun n => ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ∣ n))
      ⊆ d.primeFactors.biUnion (fun p => (bProdSet x M Y).filter (fun n => p ∣ n)) := by
    intro n hn
    obtain ⟨hnB, p, hpp, hpd, hpn⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_biUnion.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hpp, hpd, ne_of_gt hd⟩,
      Finset.mem_filter.mpr ⟨hnB, hpn⟩⟩
  calc ((bProdSet x M Y).filter (fun n => ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p ∣ n)).card
      ≤ (d.primeFactors.biUnion (fun p => (bProdSet x M Y).filter (fun n => p ∣ n))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ d.primeFactors, ((bProdSet x M Y).filter (fun n => p ∣ n)).card :=
        Finset.card_biUnion_le

/-- Every prime divisor of an element of `B̄` is at least `M` (when `M ≤ Y`). -/
lemma prime_dvd_bProdSet_ge (x M Y p n : ℕ) (hp : p.Prime) (hn : n ∈ bProdSet x M Y)
    (hpn : p ∣ n) (hMY : M ≤ Y) : M ≤ p := by
  rw [mem_bProdSet] at hn
  obtain ⟨t, ht, rfl⟩ := hn
  obtain ⟨h1, h2, h3, hMq, -, hYq2, hq2q3, -⟩ := mem_bTripleSet.mp ht
  have hdvd : p ∣ t.1 * t.2.1 * t.2.2 := hpn
  rw [mul_assoc] at hdvd
  rcases (hp.dvd_mul.mp hdvd) with hd | hd3
  · exact le_trans hMq (le_of_eq ((h1.dvd_iff_eq hp.ne_one).mp hd))
  · rcases (hp.dvd_mul.mp hd3) with hd2 | hd3'
    · exact le_trans (le_trans hMY hYq2) (le_of_eq ((h2.dvd_iff_eq hp.ne_one).mp hd2))
    · exact le_trans (le_trans hMY (le_trans hYq2 hq2q3))
        (le_of_eq ((h3.dvd_iff_eq hp.ne_one).mp hd3'))

/-- For a prime `p < M` nothing in `B̄` is divisible by `p`. -/
lemma card_filter_dvd_eq_zero (x M Y p : ℕ) (hp : p.Prime) (hMY : M ≤ Y) (hpM : p < M) :
    ((bProdSet x M Y).filter (fun n => p ∣ n)).card = 0 := by
  rw [Finset.card_eq_zero]
  ext n
  constructor
  · intro hn
    exact absurd (prime_dvd_bProdSet_ge x M Y p n hp (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2 hMY) (by omega)
  · intro hn
    exact absurd hn (Finset.notMem_empty n)

/-- The number of elements of `B̄` divisible by `p` is at most `(x+2)/p`. -/
lemma card_filter_dvd_le (x M Y p : ℕ) :
    ((bProdSet x M Y).filter (fun n => p ∣ n)).card ≤ (x + 2) / p := by
  have hinj : Set.InjOn (fun n : ℕ => n / p) ↑((bProdSet x M Y).filter (fun n => p ∣ n)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have hab' : a / p = b / p := hab
    have ha' : a = p * (a / p) := (Nat.mul_div_cancel' ha.2).symm
    have hb' : b = p * (b / p) := (Nat.mul_div_cancel' hb.2).symm
    rw [ha', hb', hab']
  have hsub : ((bProdSet x M Y).filter (fun n => p ∣ n)).image (fun n => n / p)
      ⊆ Finset.Icc 1 ((x + 2) / p) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    obtain ⟨hnB, hpn⟩ := Finset.mem_filter.mp hn
    have hnI : n ∈ Finset.Icc 2 (x + 2) := bProdSet_subset_Icc x M Y hnB
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnD : n ≤ x + 2 := (Finset.mem_Icc.mp hnI).2
    have hk : 1 ≤ n / p := by
      rcases Nat.eq_zero_or_pos (n / p) with h | h
      · exfalso
        have h' := Nat.mul_div_cancel' hpn
        rw [h, mul_zero] at h'
        omega
      · exact h
    exact Finset.mem_Icc.mpr ⟨hk, Nat.div_le_div_right hnD⟩
  calc ((bProdSet x M Y).filter (fun n => p ∣ n)).card
      = (((bProdSet x M Y).filter (fun n => p ∣ n)).image (fun n => n / p)).card := by
        rw [Finset.card_image_iff.mpr hinj]
    _ ≤ (Finset.Icc 1 ((x + 2) / p)).card := Finset.card_le_card hsub
    _ = (x + 2) / p := by simp

/-- Telescoping bound for the prime-reciprocal tail. -/
lemma sum_inv_mul_pred_le (M D : ℕ) (hM : 2 ≤ M) :
    (∑ n ∈ Finset.Icc M D, (1:ℝ)/((n:ℝ)*((n:ℝ)-1))) ≤ 2/(M:ℝ) := by
  have hMpos : (0:ℝ) < (M:ℝ) - 1 := by
    have h2 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  have htel2 : ∀ n ∈ Finset.Icc M D,
      (1:ℝ)/((n:ℝ)*((n:ℝ)-1)) = 1/((n:ℝ)-1) - 1/(n:ℝ) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans hM (Finset.mem_Icc.mp hn).1
    have h1 : (0:ℝ) < (n:ℝ) - 1 := by
      have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
      linarith
    have h2 : (0:ℝ) < (n:ℝ) := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl htel2,
    show Finset.Icc M D = Finset.Ico M (D + 1) from by
      rw [← Finset.Ico_succ_right_eq_Icc M D]; rfl,
    Finset.sum_Ico_eq_sum_range]
  have hstep : ∀ k : ℕ, (1:ℝ)/((((M+k:ℕ)):ℝ)-1) - 1/(((M+k:ℕ)):ℝ)
      = (1:ℝ)/(((M:ℝ)-1)+(k:ℝ)) - 1/(((M:ℝ)-1)+(((k+1:ℕ)):ℝ)) := by
    intro k
    have h1 : (((M+k:ℕ)):ℝ) = (M:ℝ)+k := by push_cast; ring
    have h2 : (((k+1:ℕ)):ℝ) = (k:ℝ)+1 := by push_cast; ring
    rw [h1, h2]
    ring
  rw [Finset.sum_congr rfl (fun k hk => hstep k),
    Finset.sum_range_sub' (fun k : ℕ => (1:ℝ)/(((M:ℝ)-1)+(k:ℝ))) ((D + 1) - M)]
  simp only [Nat.cast_zero, add_zero]
  have hle1 : 1/((M:ℝ)-1) - 1/(((M:ℝ)-1)+(((D + 1) - M : ℕ)) : ℝ) ≤ 1/((M:ℝ)-1) := by
    have : (0:ℝ) ≤ 1/(((M:ℝ)-1)+(((D + 1) - M : ℕ)) : ℝ) := by
      apply div_nonneg (by norm_num)
      positivity
    linarith
  refine le_trans hle1 ?_
  rw [div_le_div_iff₀ hMpos (by linarith : (0:ℝ) < (M:ℝ))]
  have h2 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  linarith

/-! ## 4. The inner sum over the multiples of a prime -/

/-- The sieve-weighted sum over the moduli divisible by a prime `p`. -/
lemma sum_totient_recip_of_prime_dvd_le (p D : ℕ) (hp : p.Prime) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
        (3:ℝ) ^ (d.primeFactors.card) / (d.totient : ℝ))
      ≤ (3 / ((p:ℝ) - 1)) *
          (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) := by
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by
    have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hinj : Set.InjOn (fun d : ℕ => d / p)
      ↑((Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have hpa : p ∣ a := (Nat.mem_primeFactors.mp ha.2).2.1
    have hpb : p ∣ b := (Nat.mem_primeFactors.mp hb.2).2.1
    have hab' : a / p = b / p := hab
    have ha' : a = p * (a / p) := (Nat.mul_div_cancel' hpa).symm
    have hb' : b = p * (b / p) := (Nat.mul_div_cancel' hpb).symm
    rw [ha', hb', hab']
  have hsub : ((Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors)).image (fun d => d / p)
      ⊆ Finset.Icc 1 D := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    obtain ⟨hdI, hpd⟩ := Finset.mem_filter.mp hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hdd : p ∣ d := (Nat.mem_primeFactors.mp hpd).2.1
    have hdeq : d = p * (d / p) := (Nat.mul_div_cancel' hdd).symm
    have hk : 1 ≤ d / p := by
      rcases Nat.eq_zero_or_pos (d / p) with h | h
      · exfalso
        rw [h, mul_zero] at hdeq
        omega
      · exact h
    exact Finset.mem_Icc.mpr ⟨hk, le_trans (Nat.div_le_self d p) (Finset.mem_Icc.mp hdI).2⟩
  have hterm : ∀ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
      (3:ℝ) ^ (d.primeFactors.card) / (d.totient : ℝ)
        ≤ (3 / ((p:ℝ) - 1)) *
            ((3:ℝ) ^ ((d / p).primeFactors.card) / ((d / p).totient : ℝ)) := by
    intro d hd
    obtain ⟨hdI, hpd⟩ := Finset.mem_filter.mp hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hpdvd : p ∣ d := (Nat.mem_primeFactors.mp hpd).2.1
    set m := d / p with hm
    have hdm : d = p * m := (Nat.mul_div_cancel' hpdvd).symm
    have hm0 : m ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hdm
      omega
    have hω : d.primeFactors.card ≤ m.primeFactors.card + 1 := by
      rw [hdm, Nat.primeFactors_mul hp.ne_zero hm0, hp.primeFactors]
      have hcu := Finset.card_union_le ({p} : Finset ℕ) m.primeFactors
      simpa [Nat.add_comm] using hcu
    have hφ : ((p:ℝ) - 1) * (m.totient : ℝ) ≤ (d.totient : ℝ) := by
      have hsuper := Nat.totient_super_multiplicative p m
      rw [Nat.totient_prime hp] at hsuper
      rw [hdm]
      have hcast : ((p - 1 : ℕ) : ℝ) * (m.totient : ℝ) ≤ ((p * m).totient : ℝ) := by
        exact_mod_cast hsuper
      have hpc : ((p - 1 : ℕ) : ℝ) = (p:ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ p by have h2 := hp.two_le; omega), Nat.cast_one]
      rwa [hpc] at hcast
    have hφpos : (0:ℝ) < (d.totient:ℝ) := by
      have hd0 : 0 < d := by
        have h1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
        omega
      have hpos : 0 < d.totient := Nat.totient_pos.mpr hd0
      exact_mod_cast hpos
    have hφmpos : (0:ℝ) < (m.totient:ℝ) := by
      have hpos : 0 < m.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)
      exact_mod_cast hpos
    have h3 : (3:ℝ) ^ (d.primeFactors.card) ≤ 3 * (3:ℝ) ^ (m.primeFactors.card) := by
      calc (3:ℝ) ^ (d.primeFactors.card) ≤ (3:ℝ) ^ (m.primeFactors.card + 1) :=
            pow_le_pow_right₀ (by norm_num) hω
        _ = 3 * (3:ℝ) ^ (m.primeFactors.card) := by rw [pow_succ]; ring
    rw [div_le_iff₀ hφpos]
    have haux : (3 / ((p:ℝ) - 1)) * ((3:ℝ) ^ (m.primeFactors.card) / (m.totient:ℝ)) *
        (((p:ℝ) - 1) * (m.totient:ℝ)) = 3 * (3:ℝ) ^ (m.primeFactors.card) := by
      field_simp <;> ring
    have hnn : (0:ℝ) ≤ (3 / ((p:ℝ) - 1)) * ((3:ℝ) ^ (m.primeFactors.card) / (m.totient:ℝ)) := by
      apply mul_nonneg
      · exact div_nonneg (by norm_num) (le_of_lt hp1)
      · exact div_nonneg (by positivity) (le_of_lt hφmpos)
    calc (3:ℝ) ^ (d.primeFactors.card)
        ≤ 3 * (3:ℝ) ^ (m.primeFactors.card) := h3
      _ = (3 / ((p:ℝ) - 1)) * ((3:ℝ) ^ (m.primeFactors.card) / (m.totient:ℝ)) *
            (((p:ℝ) - 1) * (m.totient:ℝ)) := haux.symm
      _ ≤ (3 / ((p:ℝ) - 1)) * ((3:ℝ) ^ (m.primeFactors.card) / (m.totient:ℝ)) *
            (d.totient:ℝ) := mul_le_mul_of_nonneg_left hφ hnn
  calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
        (3:ℝ) ^ (d.primeFactors.card) / (d.totient : ℝ))
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
          (3 / ((p:ℝ) - 1)) *
            ((3:ℝ) ^ ((d / p).primeFactors.card) / ((d / p).totient : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (3 / ((p:ℝ) - 1)) *
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
            ((3:ℝ) ^ ((d / p).primeFactors.card) / ((d / p).totient : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ = (3 / ((p:ℝ) - 1)) *
          ∑ m ∈ ((Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors)).image
                (fun d => d / p),
            ((3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) := by
        rw [Finset.sum_image hinj]
    _ ≤ (3 / ((p:ℝ) - 1)) *
          ∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => by positivity)
        · exact div_nonneg (by norm_num) (le_of_lt hp1)

/-! ## 5. The main sum bound -/

/-- Exchange the sum over `d` with the sum over the prime divisors of `d`. -/
lemma sum_sum_primeFactors_le (S : Finset ℕ) (D : ℕ) (hS : S ⊆ Finset.Icc 1 D)
    (g : ℕ → ℕ → ℝ) (hg : ∀ d p, 0 ≤ g d p) :
    (∑ d ∈ S, ∑ p ∈ d.primeFactors, g d p)
      ≤ ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors), g d p := by
  have h1 : ∀ d ∈ S, (∑ p ∈ d.primeFactors, g d p)
      = ∑ p ∈ Finset.Icc 1 D, (if p ∈ d.primeFactors then g d p else 0) := by
    intro d hd
    have hsub : d.primeFactors ⊆ Finset.Icc 1 D := by
      intro p hp
      obtain ⟨hpp, hpd, hd0⟩ := Nat.mem_primeFactors.mp hp
      have hple : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hpd
      have hdD : d ≤ D := (Finset.mem_Icc.mp (hS hd)).2
      exact Finset.mem_Icc.mpr ⟨by have := hpp.two_le; omega, le_trans hple hdD⟩
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  calc (∑ d ∈ S, ∑ p ∈ d.primeFactors, g d p)
      = ∑ d ∈ S, ∑ p ∈ Finset.Icc 1 D, (if p ∈ d.primeFactors then g d p else 0) :=
        Finset.sum_congr rfl h1
    _ = ∑ p ∈ Finset.Icc 1 D, ∑ d ∈ S, (if p ∈ d.primeFactors then g d p else 0) :=
        Finset.sum_comm
    _ = ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          ∑ d ∈ S, (if p ∈ d.primeFactors then g d p else 0) := by
        refine (Finset.sum_congr rfl ?_).trans (Finset.sum_filter _ _).symm
        intro p hp
        by_cases hpp : Nat.Prime p
        · rw [if_pos hpp]
        · rw [if_neg hpp]
          exact Finset.sum_eq_zero (fun d hd => by
            rw [if_neg (fun hmem => hpp (Nat.prime_of_mem_primeFactors hmem))])
    _ = ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          ∑ d ∈ S.filter (fun d => p ∈ d.primeFactors), g d p := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors), g d p := by
        refine Finset.sum_le_sum ?_
        intro p hp
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d hd _ => hg d p)
        intro d hd
        exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2⟩

/-- **The main elementary bound.**  The `3 ^ (ω d)/φ(d)`-weighted shared mass up to level `D`
is at most `3 (x+2) (∑_{m ≤ D} 3 ^ (ω m)/φ m) · 2/M`. -/
lemma bShared_sum_le (x M Y D : ℕ) (hMY : M ≤ Y) (hM2 : 2 ≤ M) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1),
        (3:ℝ) ^ (d.primeFactors.card) *
          ((bShared x M Y d : ℝ) / (d.totient : ℝ)))
      ≤ 3 * ((x:ℝ) + 2) *
          (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) *
            (2/(M:ℝ)) := by
  have hTsub : (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1) ⊆ Finset.Icc 1 D :=
    Finset.filter_subset _ _
  have hstepA : (∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1),
        (3:ℝ) ^ (d.primeFactors.card) * ((bShared x M Y d : ℝ) / (d.totient : ℝ)))
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1),
          ∑ p ∈ d.primeFactors,
            ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
              (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (hTsub hd)).1
    have hb : bShared x M Y d
        ≤ ∑ p ∈ d.primeFactors, ((bProdSet x M Y).filter (fun n => p ∣ n)).card :=
      bShared_le_sum_primeFactors x M Y d hd1
    have hcast : (bShared x M Y d : ℝ)
        ≤ ((∑ p ∈ d.primeFactors,
            ((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℕ) : ℝ) := by
      exact_mod_cast hb
    have hnonneg : (0:ℝ) ≤ (3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ) := by positivity
    calc (3:ℝ) ^ (d.primeFactors.card) * ((bShared x M Y d : ℝ) / (d.totient : ℝ))
        = ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) * (bShared x M Y d : ℝ) := by ring
      _ ≤ ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
            ((∑ p ∈ d.primeFactors,
              ((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hcast hnonneg
      _ = ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
            (∑ p ∈ d.primeFactors,
              (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ)) := by
          rw [Nat.cast_sum]
      _ = ∑ p ∈ d.primeFactors,
            ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
              (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) :=
          Finset.mul_sum _ _ _
  have hstepB := sum_sum_primeFactors_le ((Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1)) D hTsub
    (fun d p => ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
      (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ))
    (fun d p => by positivity)
  have hstepC : (∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
          ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
            (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ))
      ≤ ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) * (3 / ((p:ℝ)-1)) *
            (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hinner := sum_totient_recip_of_prime_dvd_le p D hpp
    have hNnn : (0:ℝ) ≤ (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) := by positivity
    calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
            ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
              (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ))
        = (∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
              ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ))) *
            (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ ((3 / ((p:ℝ)-1)) *
            (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ))) *
            (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) :=
          mul_le_mul_of_nonneg_right hinner hNnn
      _ = (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) * (3 / ((p:ℝ)-1)) *
            (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) := by ring
  have hstepD : (∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) * (3 / ((p:ℝ)-1)) *
            (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)))
      ≤ 3 * ((x:ℝ) + 2) *
          (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) *
            (2/(M:ℝ)) := by
    set G := ∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ) with hG
    have hGnn : (0:ℝ) ≤ G := by
      rw [hG]
      positivity
    have hdrop : (∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) * (3 / ((p:ℝ)-1)) * G)
        = ∑ p ∈ ((Finset.Icc 1 D).filter Nat.Prime).filter (fun p => M ≤ p),
            (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) * (3 / ((p:ℝ)-1)) * G := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro p hp
        exact (Finset.mem_filter.mp hp).1
      · intro p hp hnot
        have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
        have hpM : p < M := by
          by_contra hcon
          exact hnot (Finset.mem_filter.mpr ⟨hp, not_lt.mp hcon⟩)
        rw [card_filter_dvd_eq_zero x M Y p hpp hMY hpM]
        ring
    rw [hdrop]
    have hbound1 : (∑ p ∈ ((Finset.Icc 1 D).filter Nat.Prime).filter (fun p => M ≤ p),
          (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) * (3 / ((p:ℝ)-1)) * G)
        ≤ ∑ p ∈ ((Finset.Icc 1 D).filter Nat.Prime).filter (fun p => M ≤ p),
            3 * ((x:ℝ) + 2) * G * (1/((p:ℝ)*((p:ℝ)-1))) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      have hpP : p ∈ (Finset.Icc 1 D).filter Nat.Prime := (Finset.mem_filter.mp hp).1
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hpP).2
      have hp2 : 2 ≤ p := hpp.two_le
      have hp1pos : (0:ℝ) < (p:ℝ) - 1 := by
        have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
        linarith
      have hNle : (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) ≤ ((x:ℝ)+2)/(p:ℝ) := by
        have h := card_filter_dvd_le x M Y p
        calc ((((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℕ) : ℝ)
            ≤ (((x + 2) / p : ℕ) : ℝ) := by exact_mod_cast h
          _ ≤ ((x + 2 : ℕ) : ℝ) / ((p : ℕ) : ℝ) := Nat.cast_div_le
          _ = ((x:ℝ) + 2) / (p:ℝ) := by push_cast; ring
      have hp0 : ((p:ℝ)) ≠ 0 := by
        have : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
        exact ne_of_gt this
      have hp1n : (p:ℝ) - 1 ≠ 0 := ne_of_gt hp1pos
      calc (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) * (3 / ((p:ℝ)-1)) * G
          ≤ (((x:ℝ)+2)/(p:ℝ)) * (3 / ((p:ℝ)-1)) * G := by
            apply mul_le_mul_of_nonneg_right _ hGnn
            exact mul_le_mul_of_nonneg_right hNle (div_nonneg (by norm_num) (le_of_lt hp1pos))
        _ = 3 * ((x:ℝ) + 2) * G * (1/((p:ℝ)*((p:ℝ)-1))) := by
            field_simp <;> ring
    refine le_trans hbound1 ?_
    have hsub2 : ((Finset.Icc 1 D).filter Nat.Prime).filter (fun p => M ≤ p) ⊆ Finset.Icc M D := by
      intro p hp
      obtain ⟨hpP, hpM⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨hpM, (Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1).2⟩
    have hsum2 : (∑ p ∈ ((Finset.Icc 1 D).filter Nat.Prime).filter (fun p => M ≤ p),
          (1:ℝ)/((p:ℝ)*((p:ℝ)-1))) ≤ 2/(M:ℝ) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub2 ?_) (sum_inv_mul_pred_le M D hM2)
      intro p hp hnot
      have hp2 : 2 ≤ p := le_trans hM2 (Finset.mem_Icc.mp hp).1
      have h1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
      have h2 : (0:ℝ) < (p:ℝ) - 1 := by
        have h3 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
        linarith
      positivity
    have hconst : (0:ℝ) ≤ 3 * ((x:ℝ) + 2) * G :=
      mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hGnn
    calc (∑ p ∈ ((Finset.Icc 1 D).filter Nat.Prime).filter (fun p => M ≤ p),
            3 * ((x:ℝ) + 2) * G * (1/((p:ℝ)*((p:ℝ)-1))))
        = 3 * ((x:ℝ) + 2) * G *
            (∑ p ∈ ((Finset.Icc 1 D).filter Nat.Prime).filter (fun p => M ≤ p),
              1/((p:ℝ)*((p:ℝ)-1))) := (Finset.mul_sum _ _ _).symm
      _ ≤ 3 * ((x:ℝ) + 2) * G * (2/(M:ℝ)) := mul_le_mul_of_nonneg_left hsum2 hconst
  calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1),
        (3:ℝ) ^ (d.primeFactors.card) * ((bShared x M Y d : ℝ) / (d.totient : ℝ)))
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1),
          ∑ p ∈ d.primeFactors,
            ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
              (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) := hstepA
    _ ≤ ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => p ∈ d.primeFactors),
            ((3:ℝ) ^ (d.primeFactors.card) / (d.totient:ℝ)) *
              (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) := hstepB
    _ ≤ ∑ p ∈ (Finset.Icc 1 D).filter Nat.Prime,
          (((bProdSet x M Y).filter (fun n => p ∣ n)).card : ℝ) * (3 / ((p:ℝ)-1)) *
            (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) := hstepC
    _ ≤ 3 * ((x:ℝ) + 2) *
          (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) *
            (2/(M:ℝ)) := hstepD

/-- `chenSiftLimit x ≤ chenWindowTop x` for `x ≥ 1`. -/
lemma chenSiftLimit_le_chenWindowTop (x : ℕ) (hx : 1 ≤ x) :
    Submission.chenSiftLimit x ≤ Submission.chenWindowTop x := by
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hcut : cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1 = (x:ℝ) ^ (sieveAlpha/8) := by
    unfold cut
    rw [pow_one, show Real.rpow (x:ℝ) ((1:ℝ)/8) = (x:ℝ) ^ ((1:ℝ)/8) from rfl,
      ← Real.rpow_mul hx0]
    congr 1
    ring
  have hfloor : ⌊cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1⌋₊ ≤ ⌊(x:ℝ) ^ ((1:ℝ)/3)⌋₊ := by
    rw [hcut]
    apply Nat.floor_le_floor
    apply Real.rpow_le_rpow_of_exponent_le hx1
    rw [sieveAlpha]
    norm_num
  rw [Submission.chenSiftLimit, Submission.chenWindowTop,
    show Real.rpow (x:ℝ) ((1:ℝ)/3) = (x:ℝ) ^ ((1:ℝ)/3) from rfl]
  omega

/-- `chenSiftLimit x ≥ 2` for `x ≥ 1`. -/
lemma two_le_chenSiftLimit (x : ℕ) (hx : 1 ≤ x) : 2 ≤ Submission.chenSiftLimit x := by
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hcut : cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1 = (x:ℝ) ^ (sieveAlpha/8) := by
    unfold cut
    rw [pow_one, show Real.rpow (x:ℝ) ((1:ℝ)/8) = (x:ℝ) ^ ((1:ℝ)/8) from rfl,
      ← Real.rpow_mul hx0]
    congr 1
    ring
  have hone : (1:ℝ) ≤ (x:ℝ) ^ (sieveAlpha/8) := by
    apply Real.one_le_rpow hx1
    rw [sieveAlpha]
    norm_num
  rw [Submission.chenSiftLimit]
  have h1 : 0 < ⌊cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1⌋₊ := by
    rw [hcut]
    exact Nat.floor_pos.mpr hone
  omega

theorem bSharedLevelOfDistribution :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
      Filter.Eventually (fun x : ℕ =>
        Finset.sum
          ((Finset.Icc 1 (Nat.floor (Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B))).filter
            (fun d : ℕ => d % 2 = 1))
          (fun d => (3 : ℝ) ^ (d.primeFactors.card) *
            ((Work.NumberTheory.Chen.BTermCount.bShared x (Submission.chenSiftLimit x)
              (Submission.chenWindowTop x) d : ℝ) / (Nat.totient d : ℝ)))
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) Filter.atTop := by
  intro A hA
  refine ⟨1, by norm_num, ?_⟩
  set N : ℕ := Nat.ceil A with hNdef
  have hA_N : A ≤ (N:ℝ) := Nat.le_ceil A
  set C : ℝ := 12 * 2^(N+6) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    positivity
  have hlim : Filter.Tendsto (fun y : ℝ => Real.log y ^ (14 * (N + 6)) / y)
      Filter.atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 (14 * (N + 6)) one_ne_zero
  have hlimN : Filter.Tendsto (fun x : ℕ => Real.log (x:ℝ) ^ (14 * (N + 6)) / (x:ℝ))
      Filter.atTop (𝓝 0) :=
    hlim.comp tendsto_natCast_atTop_atTop
  have hpowlim : ∀ᶠ x : ℕ in Filter.atTop,
      C * (Real.log (x:ℝ)) ^ (N + 6) ≤ (x:ℝ) ^ ((1:ℝ)/14) := by
    have hc : (0:ℝ) < (1/C)^14 := by positivity
    filter_upwards [hlimN.eventually (Iio_mem_nhds hc), eventually_ge_atTop 1] with x hx hx1
    have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx1
    have hlog0 : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg (by exact_mod_cast hx1)
    have h1 : Real.log (x:ℝ) ^ (14*(N+6)) < ((1/C)^14) * (x:ℝ) :=
      (div_lt_iff₀ hx0).mp hx
    have hstep : C^14 * (Real.log (x:ℝ)) ^ (14*(N+6)) ≤ (x:ℝ) := by
      have h2 := mul_lt_mul_of_pos_left h1 (pow_pos hCpos 14)
      have h3 : C^14 * (((1/C)^14) * (x:ℝ)) = (x:ℝ) := by
        have hC1 : C * (1/C) = 1 := by
          rw [one_div, mul_inv_cancel₀ (ne_of_gt hCpos)]
        calc C^14 * (((1/C)^14) * (x:ℝ))
            = (x:ℝ) * (C * (1/C))^14 := by rw [mul_pow]; ring
          _ = (x:ℝ) * 1^14 := by rw [hC1]
          _ = (x:ℝ) := by rw [one_pow, mul_one]
      linarith
    have hxr : ((x:ℝ)^((1:ℝ)/14))^14 = (x:ℝ) := by
      rw [← Real.rpow_natCast ((x:ℝ)^((1:ℝ)/14)) 14, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num [Real.rpow_one]
    have hkey : (C * (Real.log (x:ℝ)) ^ (N + 6))^14 ≤ ((x:ℝ)^((1:ℝ)/14))^14 := by
      rw [hxr, mul_pow, ← pow_mul, Nat.mul_comm]
      exact hstep
    exact (pow_le_pow_iff_left₀
      (mul_nonneg (le_of_lt hCpos) (pow_nonneg hlog0 _))
      (Real.rpow_nonneg (le_of_lt hx0) _) (by norm_num : (14:ℕ) ≠ 0)).mp hkey
  have hmain : ∀ᶠ x : ℕ in Filter.atTop,
      (∑ d ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^(1:ℝ)))).filter
          (fun d : ℕ => d % 2 = 1),
        (3:ℝ) ^ (d.primeFactors.card) *
          ((bShared x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) d : ℝ) /
            (d.totient : ℝ)))
        ≤ 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^6 := by
    filter_upwards [eventually_ge_atTop 3] with x hx3
    have hx1r : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
    have hx2r : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
    have hx0 : (0:ℝ) < (x:ℝ) := by linarith
    have hlogge1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
      have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
      have h13 : (1:ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
        linarith [Real.exp_one_lt_three]
      exact le_trans h13 (Real.log_le_log (by norm_num) h3)
    have hMY : Submission.chenSiftLimit x ≤ Submission.chenWindowTop x :=
      chenSiftLimit_le_chenWindowTop x (by omega)
    have hM2 : 2 ≤ Submission.chenSiftLimit x := two_le_chenSiftLimit x (by omega)
    have hMpos : (0:ℝ) < (Submission.chenSiftLimit x : ℝ) := by
      have hpos : (0:ℕ) < Submission.chenSiftLimit x := by omega
      exact_mod_cast hpos
    set D := Nat.floor (Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^(1:ℝ)) with hDdef
    have hsum := bShared_sum_le x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) D
      hMY hM2
    have hG3 := sum_pow_three_div_totient_le D
    have hDx : D ≤ x := by
      rw [hDdef]
      have hlogpos : (0:ℝ) < Real.log (x:ℝ) := by linarith
      have hle : Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^(1:ℝ) ≤ (x:ℝ) := by
        rw [Real.rpow_one]
        rw [div_le_iff₀ hlogpos]
        have hsx : Real.sqrt (x:ℝ) ≤ (x:ℝ) := by
          have h2 : (x:ℝ) ≤ (x:ℝ)^2 := by nlinarith
          have hs := Real.sqrt_le_sqrt h2
          rwa [Real.sqrt_sq (le_of_lt hx0)] at hs
        nlinarith [Real.sqrt_nonneg (x:ℝ), hlogge1]
      have hle' : ((Nat.floor (Real.sqrt (x:ℝ)/(Real.log (x:ℝ))^(1:ℝ)) : ℕ) : ℝ) ≤ (x:ℝ) :=
        le_trans (Nat.floor_le (by positivity)) hle
      exact_mod_cast hle'
    have hlogD : Real.log (D:ℝ) ≤ Real.log (x:ℝ) := by
      rcases Nat.eq_zero_or_pos D with hD0 | hDpos
      · rw [hD0]
        simp only [Nat.cast_zero, Real.log_zero]
        linarith
      · exact Real.log_le_log (by exact_mod_cast hDpos) (by exact_mod_cast hDx)
    have hGnn : (0:ℝ) ≤ (∑ m ∈ Finset.Icc 1 D,
        (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) := by positivity
    have h2M : (0:ℝ) ≤ 2/(Submission.chenSiftLimit x : ℝ) := by positivity
    have hquot : 6 * ((x:ℝ) + 2)/(Submission.chenSiftLimit x : ℝ)
        ≤ 12 * (x:ℝ)^((13:ℝ)/14) := by
      rw [div_le_iff₀ hMpos]
      have hsplit : (x:ℝ)^((13:ℝ)/14) * (x:ℝ)^((1:ℝ)/14) = (x:ℝ) := by
        rw [← Real.rpow_add hx0]
        norm_num
      have hMrpow : (x:ℝ)^((1:ℝ)/14) ≤ (Submission.chenSiftLimit x : ℝ) :=
        chenSiftLimit_ge_rpow x
      calc 6 * ((x:ℝ) + 2) ≤ 12 * (x:ℝ) := by linarith
        _ = 12 * ((x:ℝ)^((13:ℝ)/14) * (x:ℝ)^((1:ℝ)/14)) := by rw [hsplit]
        _ ≤ 12 * ((x:ℝ)^((13:ℝ)/14) * (Submission.chenSiftLimit x : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hMrpow (by positivity)
        _ = 12 * (x:ℝ)^((13:ℝ)/14) * (Submission.chenSiftLimit x : ℝ) := by ring
    calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1),
          (3:ℝ) ^ (d.primeFactors.card) *
            ((bShared x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) d : ℝ) /
              (d.totient : ℝ)))
        ≤ 3 * ((x:ℝ) + 2) *
            (∑ m ∈ Finset.Icc 1 D, (3:ℝ) ^ (m.primeFactors.card) / (m.totient : ℝ)) *
              (2/(Submission.chenSiftLimit x : ℝ)) := hsum
      _ ≤ 3 * ((x:ℝ) + 2) * (Real.log (D:ℝ) + 1)^6 *
              (2/(Submission.chenSiftLimit x : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ h2M
          exact mul_le_mul_of_nonneg_left hG3 (by positivity)
      _ ≤ 3 * ((x:ℝ) + 2) * (Real.log (x:ℝ) + 1)^6 *
              (2/(Submission.chenSiftLimit x : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ h2M
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hp := pow_le_pow_left₀ (one_add_log_nonneg D)
            (by linarith [hlogD] : Real.log (D:ℝ) + 1 ≤ Real.log (x:ℝ) + 1) 6
          linarith
      _ ≤ 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^6 := by
          have h6 : (0:ℝ) ≤ (Real.log (x:ℝ) + 1)^6 := by positivity
          calc 3 * ((x:ℝ) + 2) * (Real.log (x:ℝ) + 1)^6 *
                (2/(Submission.chenSiftLimit x : ℝ))
              = (6 * ((x:ℝ) + 2)/(Submission.chenSiftLimit x : ℝ)) *
                  (Real.log (x:ℝ) + 1)^6 := by ring
            _ ≤ (12 * (x:ℝ)^((13:ℝ)/14)) * (Real.log (x:ℝ) + 1)^6 :=
                mul_le_mul_of_nonneg_right hquot h6
            _ = 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^6 := by ring
  have hfinal : ∀ᶠ x : ℕ in Filter.atTop,
      12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^6
        ≤ (x:ℝ)/(Real.log (x:ℝ))^A := by
    filter_upwards [hpowlim, eventually_ge_atTop 3] with x hx hx3
    have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
    have hlogge1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
      have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
      have h13 : (1:ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
        linarith [Real.exp_one_lt_three]
      exact le_trans h13 (Real.log_le_log (by norm_num) h3)
    have hlogpos : (0:ℝ) < Real.log (x:ℝ) := by linarith
    have hlog0 : (0:ℝ) ≤ Real.log (x:ℝ) := le_of_lt hlogpos
    have hbase : (1:ℝ) ≤ Real.log (x:ℝ) + 1 := by linarith
    have hcast1 : (Real.log (x:ℝ))^A ≤ (Real.log (x:ℝ) + 1)^(N:ℝ) := by
      calc (Real.log (x:ℝ))^A ≤ (Real.log (x:ℝ) + 1)^A :=
            Real.rpow_le_rpow hlog0 (by linarith) hA.le
        _ ≤ (Real.log (x:ℝ) + 1)^(N:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase hA_N
    have hmul2 : 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ))^A
        ≤ 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^((N:ℝ) + 6) := by
      have h1 : (Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ))^A
          ≤ (Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ) + 1)^(N:ℝ) :=
        mul_le_mul_of_nonneg_left hcast1 (by positivity)
      have h2 : (Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ) + 1)^(N:ℝ)
          = (Real.log (x:ℝ) + 1)^((N:ℝ) + 6) := by
        rw [← Real.rpow_natCast (Real.log (x:ℝ) + 1) 6,
          ← Real.rpow_add (by linarith : (0:ℝ) < Real.log (x:ℝ) + 1)]
        congr 1
        ring
      calc 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ))^A
          = 12 * (x:ℝ)^((13:ℝ)/14) *
              ((Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ))^A) := by ring
        _ ≤ 12 * (x:ℝ)^((13:ℝ)/14) *
              ((Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ) + 1)^(N:ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^((N:ℝ) + 6) := by rw [h2]
    have hbound : 12 * (Real.log (x:ℝ) + 1)^((N:ℝ) + 6) ≤ (x:ℝ)^((1:ℝ)/14) := by
      have hpow : (Real.log (x:ℝ) + 1)^((N:ℝ) + 6)
          ≤ 2^(N+6) * (Real.log (x:ℝ))^(N+6) := by
        have h2log : Real.log (x:ℝ) + 1 ≤ 2 * Real.log (x:ℝ) := by linarith
        rw [show ((N:ℝ) + 6) = ((N + 6 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
        calc (Real.log (x:ℝ) + 1)^(N+6) ≤ (2 * Real.log (x:ℝ))^(N+6) :=
              pow_le_pow_left₀ (by positivity) h2log (N+6)
          _ = 2^(N+6) * (Real.log (x:ℝ))^(N+6) := by rw [mul_pow]
      have hmul3 : 12 * (2^(N+6) * (Real.log (x:ℝ))^(N+6))
          = C * (Real.log (x:ℝ))^(N+6) := by
        rw [hCdef]
        ring
      calc 12 * (Real.log (x:ℝ) + 1)^((N:ℝ) + 6)
          ≤ 12 * (2^(N+6) * (Real.log (x:ℝ))^(N+6)) := by linarith
        _ = C * (Real.log (x:ℝ))^(N+6) := hmul3
        _ ≤ (x:ℝ)^((1:ℝ)/14) := hx
    have hxsplit : (x:ℝ)^((13:ℝ)/14) * (x:ℝ)^((1:ℝ)/14) = (x:ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hfin' : 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ))^A
        ≤ (x:ℝ) := by
      calc 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^6 * (Real.log (x:ℝ))^A
          ≤ 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^((N:ℝ) + 6) := hmul2
        _ ≤ (x:ℝ)^((13:ℝ)/14) * (x:ℝ)^((1:ℝ)/14) := by
            have h12 : (0:ℝ) ≤ (x:ℝ)^((13:ℝ)/14) := by positivity
            calc 12 * (x:ℝ)^((13:ℝ)/14) * (Real.log (x:ℝ) + 1)^((N:ℝ) + 6)
                = (x:ℝ)^((13:ℝ)/14) * (12 * (Real.log (x:ℝ) + 1)^((N:ℝ) + 6)) := by ring
              _ ≤ (x:ℝ)^((13:ℝ)/14) * (x:ℝ)^((1:ℝ)/14) :=
                  mul_le_mul_of_nonneg_left hbound h12
        _ = (x:ℝ) := hxsplit
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogpos A)]
    exact hfin'
  filter_upwards [hmain, hfinal] with x h1 h2
  exact le_trans h1 h2

