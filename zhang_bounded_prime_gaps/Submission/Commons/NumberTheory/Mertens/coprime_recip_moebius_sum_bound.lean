import Mathlib
import Submission.Commons.NumberTheory.Moebius.moebius_abs_le_one
import Submission.Commons.NumberTheory.Moebius.sum_prod_not_dvd

namespace Commons.NumberTheory.Mertens

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Moebius

/-- The multiples of `n` in `[1, N]` number `N / n`. -/
private lemma card_multiples_Icc (N n : ℕ) :
    ((Finset.Icc 1 N).filter (fun k => n ∣ k)).card = N / n := by
  have hset : (Finset.Icc 1 N).filter (fun k => n ∣ k)
      = (Finset.range N.succ).filter (fun k => k ≠ 0 ∧ n ∣ k) := by
    apply Finset.ext
    intro k
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by omega, by omega, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, by omega⟩, h3⟩
  rw [hset, Nat.card_multiples']

/-- For `k ≠ 0`, the Möbius sum over the divisors of `k` coprime to `d` equals
`∏_{p | k} [p | d]`. -/
private lemma sum_moebius_coprime_divisors (k d : ℕ) (hk : k ≠ 0) :
    (∑ s ∈ k.divisors.filter (fun s => Nat.Coprime s d),
        (ArithmeticFunction.moebius s : ℝ))
      = ∏ p ∈ k.primeFactors, (if p ∣ d then (1 : ℝ) else 0) := by
  classical
  have hQ : (∑ s ∈ k.divisors.filter (fun s => Nat.Coprime s d),
        (((ArithmeticFunction.moebius s : ℤ)) : ℚ))
      = ∏ p ∈ k.primeFactors, (if p ∣ d then (1 : ℚ) else 0) := by
    have h := Commons.NumberTheory.Moebius.sum_prod_not_dvd k hk ({d} : Finset ℕ)
      (fun _ => (1 : ℚ))
    rw [Finset.sum_singleton] at h
    have hcard : ∀ x : ℕ,
        (Nat.cast (((({d} : Finset ℕ).filter (fun c => Nat.Coprime c x)).sum
            (fun _ => (1 : ℕ))) : ℕ) : ℚ)
          = if Nat.Coprime x d then (1 : ℚ) else 0 := by
      intro x
      rw [Finset.filter_singleton]
      by_cases hx : Nat.Coprime x d
      · rw [if_pos (Nat.coprime_comm.mp hx), Finset.sum_singleton, if_pos hx] <;> norm_num
      · rw [if_neg (fun hh => hx (Nat.coprime_comm.mp hh)), Finset.sum_empty, if_neg hx]
          <;> norm_num
    have hprod : (∏ p ∈ k.primeFactors, (1 - 1 * (if p ∣ d then 0 else 1)))
        = ∏ p ∈ k.primeFactors, (if p ∣ d then (1 : ℚ) else 0) := by
      refine Finset.prod_congr rfl ?_
      intro p _
      by_cases hpd : p ∣ d <;> simp [hpd]
    have hsum : (∑ x ∈ k.divisors, (ArithmeticFunction.moebius x : ℚ) *
          (∏ p ∈ x.primeFactors, (1 : ℚ)) *
            (Nat.cast (((({d} : Finset ℕ).filter (fun c => Nat.Coprime c x)).sum
              (fun _ => (1 : ℕ))) : ℕ) : ℚ))
        = ∑ x ∈ k.divisors.filter (fun x => Nat.Coprime x d),
            (ArithmeticFunction.moebius x : ℚ) := by
      have hterm : ∀ x ∈ k.divisors,
          (ArithmeticFunction.moebius x : ℚ) * (∏ p ∈ x.primeFactors, (1 : ℚ)) *
              (Nat.cast (((({d} : Finset ℕ).filter (fun c => Nat.Coprime c x)).sum
                (fun _ => (1 : ℕ))) : ℕ) : ℚ)
            = if Nat.Coprime x d then (ArithmeticFunction.moebius x : ℚ) else 0 := by
        intro x _
        rw [hcard x, Finset.prod_const_one, mul_one]
        by_cases h : Nat.Coprime x d <;> simp [h]
      rw [Finset.sum_congr rfl hterm, Finset.sum_filter]
    rw [hprod, hsum] at h
    exact h.symm
  exact_mod_cast hQ

/-- The `⌊N/s⌋`-weighted Möbius sum over `s` coprime to `d` reindexes as a double
sum over `k ≤ N` of the coprime-divisor Möbius sums. -/
private lemma sum_moebius_mul_div_coprime_swap (d N : ℕ) :
    (∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s d),
        (ArithmeticFunction.moebius s : ℝ) * ((N / s : ℕ) : ℝ))
      = ∑ k ∈ Finset.Icc 1 N,
          ∑ s ∈ k.divisors.filter (fun s => Nat.Coprime s d),
            (ArithmeticFunction.moebius s : ℝ) := by
  classical
  set RF : Finset ℕ := (Finset.Icc 1 N).filter (fun s => Nat.Coprime s d) with hRF
  have hcard : ∀ s : ℕ, ((N / s : ℕ) : ℝ)
      = ∑ k ∈ (Finset.Icc 1 N).filter (fun k => s ∣ k), (1 : ℝ) := by
    intro s
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast (card_multiples_Icc N s).symm
  have hfilter : ∀ k ∈ Finset.Icc 1 N,
      RF.filter (fun s => s ∣ k) = k.divisors.filter (fun s => Nat.Coprime s d) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    ext s
    rw [Finset.mem_filter, hRF, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter,
      Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨_, _⟩, hcop⟩, hsdiv⟩
      exact ⟨⟨hsdiv, by omega⟩, hcop⟩
    · rintro ⟨⟨hsdiv, _⟩, hcop⟩
      have hsle : s ≤ k := Nat.le_of_dvd (by omega) hsdiv
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hsdiv (by omega), le_trans hsle hk.2⟩, hcop⟩, hsdiv⟩
  calc
    (∑ s ∈ RF, (ArithmeticFunction.moebius s : ℝ) * ((N / s : ℕ) : ℝ))
        = ∑ s ∈ RF, (ArithmeticFunction.moebius s : ℝ)
            * ∑ k ∈ (Finset.Icc 1 N).filter (fun k => s ∣ k), (1 : ℝ) := by
          apply Finset.sum_congr rfl; intro s _; rw [hcard s]
      _ = ∑ s ∈ RF, ∑ k ∈ (Finset.Icc 1 N).filter (fun k => s ∣ k),
            (ArithmeticFunction.moebius s : ℝ) := by
          apply Finset.sum_congr rfl; intro s _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
      _ = ∑ s ∈ RF, ∑ k ∈ Finset.Icc 1 N,
            (if s ∣ k then (ArithmeticFunction.moebius s : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro s _; rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.Icc 1 N, ∑ s ∈ RF,
            (if s ∣ k then (ArithmeticFunction.moebius s : ℝ) else 0) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.Icc 1 N,
            ∑ s ∈ k.divisors.filter (fun s => Nat.Coprime s d),
              (ArithmeticFunction.moebius s : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [← Finset.sum_filter]
          exact Finset.sum_congr (hfilter k hk) (fun _ _ => rfl)

/-- The reciprocal Möbius sum over the integers coprime to `d` is bounded by `2`. -/
private lemma coprime_recip_bound (d N : ℕ) :
    |∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s d),
        (ArithmeticFunction.moebius s : ℝ) / (s : ℝ)| ≤ 2 := by
  classical
  by_cases hN : N = 0
  · subst hN
    have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) :=
      Finset.Icc_eq_empty (by norm_num)
    rw [hempty]; simp
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  set A : Finset ℕ := (Finset.Icc 1 N).filter (fun s => Nat.Coprime s d) with hA
  set S : ℝ := ∑ s ∈ A, (ArithmeticFunction.moebius s : ℝ) / (s : ℝ) with hS
  set T : ℝ := ∑ s ∈ A, (ArithmeticFunction.moebius s : ℝ) * ((N / s : ℕ) : ℝ) with hT
  set R : ℝ := ∑ s ∈ A,
      (ArithmeticFunction.moebius s : ℝ) * ((N : ℝ) / (s : ℝ) - ((N / s : ℕ) : ℝ)) with hR
  have hdecomp : (N : ℝ) * S = T + R := by
    rw [hS, hT, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hs' := hs
    rw [hA, Finset.mem_filter, Finset.mem_Icc] at hs'
    obtain ⟨⟨hs1, _⟩, _⟩ := hs'
    have hs0 : (s : ℝ) ≠ 0 := by
      have : s ≠ 0 := by omega
      exact_mod_cast this
    field_simp
    ring
  have hRbound : |R| ≤ (N : ℝ) := by
    rw [hR]
    calc |∑ s ∈ A, (ArithmeticFunction.moebius s : ℝ)
            * ((N : ℝ) / (s : ℝ) - ((N / s : ℕ) : ℝ))|
        ≤ ∑ s ∈ A, |(ArithmeticFunction.moebius s : ℝ)
            * ((N : ℝ) / (s : ℝ) - ((N / s : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ A, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro s hs
          have hs' := hs
          rw [hA, Finset.mem_filter, Finset.mem_Icc] at hs'
          obtain ⟨⟨hs1, _⟩, _⟩ := hs'
          rw [abs_mul]
          have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
          have hcast : (s : ℝ) * ((N / s : ℕ) : ℝ) + ((N % s : ℕ) : ℝ) = (N : ℝ) := by
            have := congrArg (fun z : ℕ => (z : ℝ)) (Nat.div_add_mod N s)
            push_cast at this
            linarith [this]
          have hdiv : (N : ℝ) / (s : ℝ)
              = ((N / s : ℕ) : ℝ) + ((N % s : ℕ) : ℝ) / (s : ℝ) := by
            rw [div_eq_iff (ne_of_gt hs0), add_mul, div_mul_cancel₀ _ (ne_of_gt hs0)]
            linarith [hcast]
          have hfrac0 : 0 ≤ (N : ℝ) / (s : ℝ) - ((N / s : ℕ) : ℝ) := by
            rw [hdiv]
            have : 0 ≤ ((N % s : ℕ) : ℝ) / (s : ℝ) := by positivity
            linarith
          have hfrac1 : (N : ℝ) / (s : ℝ) - ((N / s : ℕ) : ℝ) < 1 := by
            rw [hdiv]
            have hlt := Nat.mod_lt N (by omega : 0 < s)
            have hlt' : ((N % s : ℕ) : ℝ) < (s : ℝ) := by exact_mod_cast hlt
            have : ((N % s : ℕ) : ℝ) / (s : ℝ) < 1 := by
              rw [div_lt_one hs0]; exact hlt'
            linarith
          rw [abs_of_nonneg hfrac0]
          have hmu : |(ArithmeticFunction.moebius s : ℝ)| ≤ 1 :=
            Commons.NumberTheory.Moebius.moebius_abs_le_one s
          calc |(ArithmeticFunction.moebius s : ℝ)|
                * ((N : ℝ) / (s : ℝ) - ((N / s : ℕ) : ℝ))
              ≤ 1 * 1 := mul_le_mul hmu (le_of_lt hfrac1) hfrac0 (by norm_num)
            _ = 1 := by norm_num
      _ = (A.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (N : ℝ) := by
          have hle : A.card ≤ (Finset.Icc 1 N).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          have hcardIcc : (Finset.Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
          have : A.card ≤ N := by omega
          exact_mod_cast this
  have hTbound : |T| ≤ (N : ℝ) := by
    rw [hT, hA, sum_moebius_mul_div_coprime_swap]
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        0 ≤ ∑ s ∈ k.divisors.filter (fun s => Nat.Coprime s d),
              (ArithmeticFunction.moebius s : ℝ) ∧
        (∑ s ∈ k.divisors.filter (fun s => Nat.Coprime s d),
              (ArithmeticFunction.moebius s : ℝ)) ≤ 1 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk0 : k ≠ 0 := by omega
      rw [sum_moebius_coprime_divisors k d hk0]
      constructor
      · apply Finset.prod_nonneg
        intro p _
        by_cases h : p ∣ d <;> simp [h]
      · apply Finset.prod_le_one
        · intro p _; by_cases h : p ∣ d <;> simp [h]
        · intro p _; by_cases h : p ∣ d <;> simp [h]
    have hnonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 N,
        ∑ s ∈ k.divisors.filter (fun s => Nat.Coprime s d),
          (ArithmeticFunction.moebius s : ℝ) :=
      Finset.sum_nonneg (fun k hk => (hpt k hk).1)
    have hle : (∑ k ∈ Finset.Icc 1 N,
        ∑ s ∈ k.divisors.filter (fun s => Nat.Coprime s d),
          (ArithmeticFunction.moebius s : ℝ)) ≤ (N : ℝ) := by
      calc _ ≤ ∑ _k ∈ Finset.Icc 1 N, (1 : ℝ) :=
            Finset.sum_le_sum (fun k hk => (hpt k hk).2)
        _ = (N : ℝ) := by
            have hcardIcc : (Finset.Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcardIcc]
    rw [abs_of_nonneg hnonneg]; exact hle
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hfinal : (N : ℝ) * |S| ≤ (N : ℝ) * 2 := by
    have h1 : |(N : ℝ) * S| ≤ 2 * (N : ℝ) := by
      rw [hdecomp]
      calc |T + R| ≤ |T| + |R| := abs_add_le _ _
        _ ≤ (N : ℝ) + (N : ℝ) := add_le_add hTbound hRbound
        _ = 2 * (N : ℝ) := by ring
    rw [abs_mul, abs_of_nonneg (le_of_lt hNpos)] at h1
    linarith
  exact le_of_mul_le_mul_left hfinal hNpos

theorem coprime_recip_moebius_sum_bound (d N : ℕ) :
    |∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s d),
        (ArithmeticFunction.moebius s : ℝ) / (s : ℝ)|
      ≤ 2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hbound := coprime_recip_bound d N
  have hprod : (1 : ℝ) ≤ ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    have h1 : (∏ p ∈ d.primeFactors, (1 : ℝ))
        ≤ ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_le_prod
      · intro p _; norm_num
      · intro p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          have hpP := Nat.prime_of_mem_primeFactors hp
          exact_mod_cast hpP.two_le
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
        linarith
    rwa [Finset.prod_const_one] at h1
  calc |∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s d),
        (ArithmeticFunction.moebius s : ℝ) / (s : ℝ)|
      ≤ 2 := hbound
    _ = 2 * 1 := by ring
    _ ≤ 2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)

end Commons.NumberTheory.Mertens
