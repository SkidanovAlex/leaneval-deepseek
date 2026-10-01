import Mathlib
import Submission.Commons.NumberTheory.Linnik.sum_log_div_primeFactors_le
import Submission.Commons.NumberTheory.Primes.prime_dvd_of_prime_pow_not_coprime

set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.NumberTheory.Linnik

private lemma chi_eq_indicator_mul_prim {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (n : ℕ) :
    (χ (n : ZMod q) : ℂ) =
      (if Nat.Coprime n q then (1 : ℂ) else 0) *
        (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) := by
  by_cases h : Nat.Coprime n q
  · rw [if_pos h, one_mul]
    have ha : IsCoprime (n : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    have hpc := DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := χ) (n := q) ha
    simp only [Int.cast_natCast] at hpc
    exact hpc.symm
  · rw [if_neg h, zero_mul]
    have h0 : χ ((n : ℤ) : ZMod q) = 0 :=
      (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
        (fun hh => h (Nat.isCoprime_iff_coprime.mp hh))
    simpa only [Int.cast_natCast] using h0

private lemma chi_sub_primitive_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (n : ℕ) :
    ‖(χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)‖
      ≤ (if Nat.Coprime n q then 0 else 1) := by
  have h := chi_eq_indicator_mul_prim χ n
  rw [h]
  have hsplit : (if Nat.Coprime n q then (1 : ℂ) else 0) *
        (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)
      - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)
      = ((if Nat.Coprime n q then (1 : ℂ) else 0) - 1) *
        (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) := by ring
  rw [hsplit, norm_mul]
  have h1 : ‖((if Nat.Coprime n q then (1 : ℂ) else 0) - 1)‖ = (if Nat.Coprime n q then 0 else 1) := by
    by_cases hc : Nat.Coprime n q
    · rw [if_pos hc, if_pos hc]; norm_num
    · rw [if_neg hc, if_neg hc]; norm_num
  have h2 : ‖(χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)‖ ≤ 1 :=
    DirichletCharacter.norm_le_one _ _
  rw [h1]
  calc (if Nat.Coprime n q then 0 else 1) *
        ‖(χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)‖
      ≤ (if Nat.Coprime n q then 0 else 1) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by split_ifs <;> norm_num)
    _ = (if Nat.Coprime n q then 0 else 1) := by ring

private lemma f_norm_le_of_support {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) {Kf : ℝ}
    (hKf : ∀ t ∈ Set.Icc 0 x₀, ‖f t‖ ≤ Kf)
    {q n : ℕ} [NeZero q] (hq1 : 1 < q) (hn : 1 ≤ n) :
    ‖f (Real.log (n : ℝ) / Real.log (q : ℝ))‖ ≤ Kf := by
  have hKf0 : 0 ≤ Kf := le_trans (norm_nonneg _) (hKf 0 ⟨le_refl 0, hx₀.le⟩)
  have hn0 : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hqpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have ht0 : 0 ≤ Real.log (n : ℝ) / Real.log (q : ℝ) := div_nonneg hn0 hqpos.le
  by_cases ht : x₀ ≤ Real.log (n : ℝ) / Real.log (q : ℝ)
  · rw [hsupp _ ht]; simpa using hKf0
  · exact hKf _ ⟨ht0, le_of_lt (not_le.mp ht)⟩

private lemma two_rpow_neg_half_le : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 7 / 8 := by
  have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2, inv_le_comm₀ (Real.sqrt_pos.mpr (by norm_num)) (by norm_num : (0 : ℝ) < 7 / 8)]
  rw [show ((7 : ℝ) / 8)⁻¹ = 8 / 7 by norm_num]
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

private lemma vonMangoldt_nonCoprime_geom_le (q N : ℕ) (hq : 100 ≤ q) {σ : ℝ}
    (hσ : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ σ) :
    (∑ n ∈ Finset.range N,
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          (if Nat.Coprime n q then 0 else 1) * ((n : ℝ) ^ (-σ)))
      ≤ 8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) *
          (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) := by
  have hq0 : q ≠ 0 := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqR1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hqR1
  have hlog100 : (4 : ℝ) ≤ Real.log (100 : ℝ) := by
    have h1 : Real.log (100 : ℝ) = 2 * Real.log 10 := by
      rw [show (100 : ℝ) = (10 : ℝ) ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h1]
    have h2 : Real.log (8 : ℝ) ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
    have h3 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h3] at h2
    nlinarith [Real.log_two_gt_d9]
  have hlogq4 : (4 : ℝ) ≤ Real.log (q : ℝ) :=
    le_trans hlog100 (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (q : ℝ)) := Real.log_nonneg (by linarith)
  set ε : ℝ := Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) with hε
  have hε_nonneg : 0 ≤ ε := div_nonneg (Real.sqrt_nonneg _) hlogq_pos.le
  have hε_le_half : ε ≤ 1 / 2 := by
    rw [hε, div_le_iff₀ hlogq_pos]
    have hll : Real.log (Real.log (q : ℝ)) ≤ Real.log (q : ℝ) := by
      have := Real.log_le_sub_one_of_pos hlogq_pos
      linarith
    have hsq : Real.log (q : ℝ) ≤ (Real.log (q : ℝ)) ^ 2 / 4 := by
      nlinarith [hlogq4, hlogq_pos]
    have hs : Real.sqrt (Real.log (Real.log (q : ℝ))) ≤ Real.log (q : ℝ) / 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    linarith
  have hσ_pos : 0 < σ := by linarith
  have hqε : (q : ℝ) ^ ε = Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) := by
    rw [hε, Real.rpow_def_of_pos hqR]
    congr 1
    field_simp
  have hDS_nonneg : ∀ n : ℕ, 0 ≤ ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N,
      (if n = p ^ k then Real.log (p : ℝ) * (n : ℝ) ^ (-σ) else 0) := by
    intro n
    apply Finset.sum_nonneg; intro p hp
    apply Finset.sum_nonneg; intro k hk
    by_cases h : n = p ^ k
    · rw [if_pos h]
      exact mul_nonneg (Real.log_nonneg (by
        have := Nat.prime_of_mem_primeFactors hp
        exact_mod_cast this.one_le)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · rw [if_neg h]
  have hterm : ∀ n ∈ Finset.range N,
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        (if Nat.Coprime n q then 0 else 1) * ((n : ℝ) ^ (-σ))
      ≤ ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N,
          (if n = p ^ k then Real.log (p : ℝ) * ((n : ℝ) ^ (-σ)) else 0) := by
    intro n hn
    rw [Finset.mem_range] at hn
    by_cases hc : Nat.Coprime n q
    · rw [if_pos hc, mul_zero, zero_mul]
      exact hDS_nonneg n
    · rw [if_neg hc, mul_one]
      by_cases hpp : IsPrimePow n
      · obtain ⟨p0, k0, hp0, hk0, hnk⟩ := (isPrimePow_nat_iff n).mp hpp
        have hdq : p0 ∣ q :=
          Commons.NumberTheory.Primes.prime_dvd_of_prime_pow_not_coprime hp0 hk0 hnk hc
        have hmemP : p0 ∈ q.primeFactors := Nat.Prime.mem_primeFactors hp0 hdq hq0
        have hk0le : k0 ≤ N := by
          have h2 : 2 ^ k0 ≤ n := by rw [← hnk]; exact Nat.pow_le_pow_left hp0.two_le k0
          have hlt : k0 < 2 ^ k0 := Nat.lt_two_pow_self
          omega
        have hmemk : k0 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hk0, hk0le⟩
        have hΛ : ArithmeticFunction.vonMangoldt n = Real.log (p0 : ℝ) := by
          rw [← hnk, ArithmeticFunction.vonMangoldt_apply_pow hk0.ne',
            ArithmeticFunction.vonMangoldt_apply_prime hp0]
        rw [hΛ]
        have hlogp0 : 0 ≤ Real.log (p0 : ℝ) := Real.log_nonneg (by exact_mod_cast hp0.one_le)
        have hinner : Real.log (p0 : ℝ) * (n : ℝ) ^ (-σ)
            ≤ ∑ k ∈ Finset.Icc 1 N,
                (if n = p0 ^ k then Real.log (p0 : ℝ) * (n : ℝ) ^ (-σ) else 0) := by
          have hs := Finset.single_le_sum (s := Finset.Icc 1 N)
            (f := fun k : ℕ => (if n = p0 ^ k then Real.log (p0 : ℝ) * (n : ℝ) ^ (-σ) else 0))
            (fun k _ => by
              by_cases h : n = p0 ^ k
              · rw [if_pos h]
                exact mul_nonneg hlogp0 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              · rw [if_neg h]) hmemk
          rwa [if_pos hnk.symm] at hs
        have houter : (∑ k ∈ Finset.Icc 1 N,
                (if n = p0 ^ k then Real.log (p0 : ℝ) * (n : ℝ) ^ (-σ) else 0))
            ≤ ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N,
                (if n = p ^ k then Real.log (p : ℝ) * (n : ℝ) ^ (-σ) else 0) := by
          refine Finset.single_le_sum (f := fun p : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (if n = p ^ k then Real.log (p : ℝ) * (n : ℝ) ^ (-σ) else (0 : ℝ)))
            (fun p hp => ?_) hmemP
          exact Finset.sum_nonneg (fun k _ => by
            by_cases h : n = p ^ k
            · rw [if_pos h]
              exact mul_nonneg (Real.log_nonneg (by
                have := Nat.prime_of_mem_primeFactors hp
                exact_mod_cast this.one_le)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
            · rw [if_neg h])
        exact le_trans hinner houter
      · have hΛ0 : ArithmeticFunction.vonMangoldt n = 0 := by
          rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact hpp
        rw [hΛ0]
        simp only [zero_mul]
        exact hDS_nonneg n
  have hreindex : (∑ n ∈ Finset.range N, ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N,
          (if n = p ^ k then Real.log (p : ℝ) * ((n : ℝ) ^ (-σ)) else 0))
      = ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ Finset.range N,
          (if n = p ^ k then Real.log (p : ℝ) * ((n : ℝ) ^ (-σ)) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p hp
    rw [Finset.sum_comm]
  have hper : ∀ p ∈ q.primeFactors,
      (∑ k ∈ Finset.Icc 1 N, Real.log (p : ℝ) * ((p : ℝ) ^ (-σ)) ^ k)
        ≤ Real.log (p : ℝ) / (p : ℝ) *
            (8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ))))) := by
    intro p hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
    have hpq : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.le_of_mem_primeFactors hp
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    set r : ℝ := (p : ℝ) ^ (-σ) with hr
    have hr_nonneg : 0 ≤ r := Real.rpow_nonneg hppos.le _
    have hr_lt1 : r < 1 := by
      rw [hr, ← Real.rpow_zero (p : ℝ)]
      exact (Real.rpow_lt_rpow_left_iff hp1).mpr (by simpa using hσ_pos)
    have hr_le : r ≤ 7 / 8 := by
      rw [hr]
      have h1 : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
        rw [Real.rpow_neg hppos.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hppos σ)
          (Real.rpow_pos_of_pos (by norm_num) σ)).mpr
          (Real.rpow_le_rpow (by norm_num) hp2 hσ_pos.le)
      have h2 : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(1 - ε)) :=
        (Real.rpow_le_rpow_left_iff (x := 2) (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
      have h3 : (2 : ℝ) ^ (-(1 - ε)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        (Real.rpow_le_rpow_left_iff (x := 2) (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
      exact le_trans h1 (le_trans h2 (le_trans h3 two_rpow_neg_half_le))
    have hgeom : (∑ k ∈ Finset.Icc 1 N, r ^ k) ≤ 8 * r := by
      have hIco : (∑ k ∈ Finset.Icc 1 N, r ^ k) = ∑ k ∈ Finset.Ico 1 (N + 1), r ^ k := by
        rw [Finset.Ico_add_one_right_eq_Icc]
      rw [hIco]
      have h2 := geom_sum_Ico_le_of_lt_one (x := r) hr_nonneg hr_lt1 (m := 1) (n := N + 1)
      have h3 : r ^ 1 / (1 - r) ≤ 8 * r := by
        rw [pow_one, div_le_iff₀ (by linarith : 0 < 1 - r)]
        nlinarith [hr_le, hr_nonneg]
      linarith
    have hrstuff : (p : ℝ) ^ (-σ) ≤
        Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) / (p : ℝ) := by
      have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(1 - ε)) :=
        (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)
      have h2 : (p : ℝ) ^ (-(1 - ε)) = (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ ε := by
        rw [show -(1 - ε) = -1 + ε by ring, Real.rpow_add hppos]
      have h3 : (p : ℝ) ^ (-1 : ℝ) = (p : ℝ)⁻¹ := Real.rpow_neg_one _
      have h4 : (p : ℝ) ^ ε ≤ (q : ℝ) ^ ε := Real.rpow_le_rpow hppos.le hpq hε_nonneg
      calc (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(1 - ε)) := h1
        _ = (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ ε := h2
        _ ≤ (p : ℝ) ^ (-1 : ℝ) * (q : ℝ) ^ ε :=
              mul_le_mul_of_nonneg_left h4 (by rw [h3]; positivity)
        _ = (q : ℝ) ^ ε / (p : ℝ) := by rw [h3]; ring
        _ = Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) / (p : ℝ) := by rw [hqε]
    have hcombine : Real.log (p : ℝ) * (8 * r)
        ≤ Real.log (p : ℝ) / (p : ℝ) *
            (8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ))))) := by
      have hL : Real.log (p : ℝ) * (8 * r) = 8 * (Real.log (p : ℝ) * r) := by ring
      have hR : Real.log (p : ℝ) / (p : ℝ) *
            (8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))))
          = 8 * (Real.log (p : ℝ) *
              (Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) / (p : ℝ))) := by ring
      rw [hL, hR, hr]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrstuff hlogp) (by norm_num)
    calc (∑ k ∈ Finset.Icc 1 N, Real.log (p : ℝ) * ((p : ℝ) ^ (-σ)) ^ k)
        = Real.log (p : ℝ) * (∑ k ∈ Finset.Icc 1 N, ((p : ℝ) ^ (-σ)) ^ k) := by
          rw [Finset.mul_sum]
      _ ≤ Real.log (p : ℝ) * (8 * r) := by
          apply mul_le_mul_of_nonneg_left _ hlogp
          rw [← hr]; exact hgeom
      _ ≤ Real.log (p : ℝ) / (p : ℝ) *
            (8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ))))) := hcombine
  calc (∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (if Nat.Coprime n q then 0 else 1) * ((n : ℝ) ^ (-σ)))
      ≤ ∑ n ∈ Finset.range N, ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N,
          (if n = p ^ k then Real.log (p : ℝ) * ((n : ℝ) ^ (-σ)) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ Finset.range N,
          (if n = p ^ k then Real.log (p : ℝ) * ((n : ℝ) ^ (-σ)) else 0) := hreindex
    _ ≤ ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N,
          Real.log (p : ℝ) * ((p : ℝ) ^ (-σ)) ^ k := by
        apply Finset.sum_le_sum; intro p hp
        apply Finset.sum_le_sum; intro k hk
        rw [Finset.sum_ite_eq']
        have hppos : 0 < (p : ℝ) := by
          have := Nat.prime_of_mem_primeFactors hp; exact_mod_cast this.pos
        have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
          have := Nat.prime_of_mem_primeFactors hp; exact_mod_cast this.one_le)
        by_cases hmem : p ^ k ∈ Finset.range N
        · rw [if_pos hmem]
          apply mul_le_mul_of_nonneg_left _ hlogp
          rw [Nat.cast_pow]
          have hkey : ((p : ℝ) ^ k) ^ (-σ) = ((p : ℝ) ^ (-σ)) ^ k := by
            rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hppos.le (k : ℝ) (-σ),
              ← Real.rpow_natCast ((p : ℝ) ^ (-σ)) k, ← Real.rpow_mul hppos.le (-σ) (k : ℝ)]
            ring_nf
          rw [hkey]
        · rw [if_neg hmem]
          exact mul_nonneg hlogp (pow_nonneg (Real.rpow_nonneg hppos.le _) k)
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) *
            (8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ))))) :=
        Finset.sum_le_sum hper
    _ = 8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) *
          (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) := by
        rw [← Finset.sum_mul]; ring

theorem Ksum_imprimitive_diff (x₀ : ℝ) (hx₀ : 0 < x₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0))
      (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      {Kf : ℝ} (hKf : ∀ t ∈ Set.Icc 0 x₀, ‖f t‖ ≤ Kf)
      {s : ℂ}
      (hs1 : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ s.re)
      (hs2 : s.re ≤ 2),
      ‖∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)) /
          (n : ℂ) ^ s * ((f (Real.log n / Real.log (q : ℝ)) : ℝ) : ℂ)‖
        ≤ C * Kf * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) *
            (Real.log (Real.log (q : ℝ)) + 2) ^ 2 := by
  obtain ⟨Cb, hCbpos, hCbbound⟩ := sum_log_div_primeFactors_le
  refine ⟨8 * Cb, by positivity, 100, ?_⟩
  intro q hqN hq100 χ hχ f hcont hsupp Kf hKf s hs1 hs2
  have hq1 : 1 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hKf0 : 0 ≤ Kf := le_trans (norm_nonneg _) (hKf 0 ⟨le_refl 0, hx₀.le⟩)
  set N : ℕ := ⌈(q : ℝ) ^ x₀⌉₊ + 1 with hNdef
  have hN : ∀ n : ℕ, N ≤ n → x₀ ≤ Real.log (n : ℝ) / Real.log (q : ℝ) := by
    intro n hn
    have hNge : (q : ℝ) ^ x₀ ≤ (N : ℝ) := by
      rw [hNdef]
      push_cast
      have := Nat.le_ceil ((q : ℝ) ^ x₀)
      linarith
    have hnge : (q : ℝ) ^ x₀ ≤ (n : ℝ) := le_trans hNge (by exact_mod_cast hn)
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hqR x₀) hnge
    rw [Real.log_rpow hqR x₀] at hlog
    rw [le_div_iff₀ hlogq_pos]
    linarith
  let G : ℕ → ℂ := fun n =>
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        ((χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)) /
        (n : ℂ) ^ s * ((f (Real.log n / Real.log (q : ℝ)) : ℝ) : ℂ)
  show ‖∑' n, G n‖ ≤ 8 * Cb * Kf * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) *
        (Real.log (Real.log (q : ℝ)) + 2) ^ 2
  have hGzero : ∀ n : ℕ, N ≤ n → G n = 0 := by
    intro n hn
    have hf0 : f (Real.log (n : ℝ) / Real.log (q : ℝ)) = 0 := hsupp _ (hN n hn)
    simp only [G, hf0, Complex.ofReal_zero, mul_zero]
  have htsum : (∑' n, G n) = ∑ n ∈ Finset.range N, G n :=
    tsum_eq_sum (fun n hn => hGzero n (not_lt.mp (by simpa [Finset.mem_range] using hn)))
  rw [htsum]
  have hbound : ∀ n : ℕ, ‖G n‖ ≤ Kf * ((ArithmeticFunction.vonMangoldt n) *
        (if Nat.Coprime n q then 0 else 1) * ((n : ℝ) ^ (-s.re))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 :=
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
      have hG0 : G 0 = 0 := by
        simp only [G, hΛ0, Complex.ofReal_zero, zero_div, zero_mul]
      rw [hG0, hΛ0]
      simp
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hδ : ‖(χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)‖
          ≤ (if Nat.Coprime n q then 0 else 1) := chi_sub_primitive_norm_le χ n
      have hf : ‖f (Real.log (n : ℝ) / Real.log (q : ℝ))‖ ≤ Kf :=
        f_norm_le_of_support hx₀ hsupp hKf hq1 hnpos
      have hGform : G n = (ArithmeticFunction.vonMangoldt n : ℂ) *
                ((χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)) *
                ((n : ℂ) ^ s)⁻¹ * ((f (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) := by
        simp only [G]; ring
      rw [hGform]
      have hcpow : ‖(((n : ℂ) ^ s)⁻¹)‖ = (n : ℝ) ^ (-s.re) := by
        have h1 : ‖((n : ℂ) ^ s)‖ = (n : ℝ) ^ (s.re) := by
          have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := (Complex.ofReal_natCast n).symm
          rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnR]
        rw [norm_inv, h1, ← Real.rpow_neg (Nat.cast_nonneg n)]
      have hΛnorm : ‖(ArithmeticFunction.vonMangoldt n : ℝ)‖ = ArithmeticFunction.vonMangoldt n :=
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg
      have hnorms : ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
                ((χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)) *
                ((n : ℂ) ^ s)⁻¹ * ((f (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖
          = (ArithmeticFunction.vonMangoldt n) *
            ‖(χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)‖ *
            (n : ℝ) ^ (-s.re) * ‖f (Real.log (n : ℝ) / Real.log (q : ℝ))‖ := by
        rw [norm_mul, norm_mul, norm_mul, hcpow, Complex.norm_real, hΛnorm, Complex.norm_real]
      rw [hnorms]
      have hstep : (ArithmeticFunction.vonMangoldt n) *
            ‖(χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)‖ *
            (n : ℝ) ^ (-s.re) * ‖f (Real.log (n : ℝ) / Real.log (q : ℝ))‖
          ≤ Kf * ((ArithmeticFunction.vonMangoldt n) *
              (if Nat.Coprime n q then 0 else 1) * ((n : ℝ) ^ (-s.re))) := by
        have hL : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
        have hnn : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        have hif : 0 ≤ (if Nat.Coprime n q then (0 : ℝ) else 1) := by split_ifs <;> norm_num
        have h1 : (ArithmeticFunction.vonMangoldt n) *
              ‖(χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)‖ *
              (n : ℝ) ^ (-s.re)
            ≤ (ArithmeticFunction.vonMangoldt n) * (if Nat.Coprime n q then 0 else 1) *
              (n : ℝ) ^ (-s.re) := by
          apply mul_le_mul_of_nonneg_right _ hnn
          exact mul_le_mul_of_nonneg_left hδ hL
        calc (ArithmeticFunction.vonMangoldt n) *
              ‖(χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)‖ *
              (n : ℝ) ^ (-s.re) * ‖f (Real.log (n : ℝ) / Real.log (q : ℝ))‖
            ≤ (ArithmeticFunction.vonMangoldt n) * (if Nat.Coprime n q then 0 else 1) *
              (n : ℝ) ^ (-s.re) * ‖f (Real.log (n : ℝ) / Real.log (q : ℝ))‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ (ArithmeticFunction.vonMangoldt n) * (if Nat.Coprime n q then 0 else 1) *
              (n : ℝ) ^ (-s.re) * Kf :=
              mul_le_mul_of_nonneg_left hf (mul_nonneg (mul_nonneg hL hif) hnn)
          _ = Kf * ((ArithmeticFunction.vonMangoldt n) *
              (if Nat.Coprime n q then 0 else 1) * ((n : ℝ) ^ (-s.re))) := by ring
      exact hstep
  calc ‖∑ n ∈ Finset.range N, G n‖
      ≤ ∑ n ∈ Finset.range N, ‖G n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, Kf * ((ArithmeticFunction.vonMangoldt n) *
          (if Nat.Coprime n q then 0 else 1) * ((n : ℝ) ^ (-s.re))) :=
        Finset.sum_le_sum (fun n _ => hbound n)
    _ = Kf * ∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n) *
          (if Nat.Coprime n q then 0 else 1) * ((n : ℝ) ^ (-s.re))) := by
        rw [← Finset.mul_sum]
    _ ≤ Kf * (8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) *
          (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hKf0
        exact vonMangoldt_nonCoprime_geom_le q N hq100 (σ := s.re) hs1
    _ ≤ Kf * (8 * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) *
          (Cb * (Real.log (Real.log (q : ℝ)) + 2) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hKf0
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hCbbound q hq100
    _ = 8 * Cb * Kf * Real.exp (Real.sqrt (Real.log (Real.log (q : ℝ)))) *
          (Real.log (Real.log (q : ℝ)) + 2) ^ 2 := by ring

end Commons.NumberTheory.Linnik
