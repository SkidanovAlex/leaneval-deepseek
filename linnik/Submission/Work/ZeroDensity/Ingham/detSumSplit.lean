import Mathlib
import Submission.Work.ZeroDensity.Ingham.detTermDef

open scoped Classical BigOperators
open MeasureTheory

namespace Work.ZeroDensity.Ingham

/-! ## Absolute summability of the summand -/

lemma detTerm_summable (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ) :
    Summable (detTerm K Y ρ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) + (-ρ.re) ≤ (k : ℝ) :=
    ⟨⌈-ρ.re⌉₊ + 1, by
      have hc := Nat.le_ceil (-ρ.re)
      push_cast
      linarith⟩
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-(1 / Y) * (n : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul k (r := 1 / Y) (by positivity)
  have hbase : Summable (fun n : ℕ => (max 1 K : ℝ) *
      ((n : ℝ) ^ k * Real.exp (-(1 / Y) * (n : ℝ)))) :=
    Summable.mul_left (max 1 K : ℝ) h0
  refine Summable.of_norm_bounded_eventually hbase ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmc : ‖mCoef K n‖ ≤ (n : ℝ) :=
    (norm_mCoef_le_tau K n).trans (by exact_mod_cast Nat.card_divisors_le_self n)
  have hnorm : ‖detTerm K Y ρ n‖
      = ‖mCoef K n‖ * (n : ℝ) ^ (-ρ.re) * Real.exp (-(n : ℝ) / Y) := by
    have hbase_rw : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by rw [← Complex.ofReal_natCast]
    simp only [detTerm]
    rw [norm_mul, norm_mul, hbase_rw,
      Complex.norm_cpow_eq_rpow_re_of_pos (x := (n : ℝ)) hnpos (-ρ), Complex.neg_re,
      Complex.norm_exp]
    rw [show (-(((n : ℝ)) : ℂ) / Y) = (((-(n : ℝ)) / Y : ℝ) : ℂ) by
      rw [Complex.ofReal_div, Complex.ofReal_neg], Complex.ofReal_re]
  rw [hnorm]
  have hexp : Real.exp (-(n : ℝ) / Y) = Real.exp (-(1 / Y) * (n : ℝ)) := by
    congr 1
    ring
  have h2 : (n : ℝ) * (n : ℝ) ^ (-ρ.re) ≤ (n : ℝ) ^ k := by
    have hEq : (n : ℝ) * (n : ℝ) ^ (-ρ.re) = (n : ℝ) ^ ((1 : ℝ) + (-ρ.re)) := by
      rw [Real.rpow_add hnpos, Real.rpow_one]
    rw [hEq, ← Real.rpow_natCast (n : ℝ) k]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hk
  calc ‖mCoef K n‖ * (n : ℝ) ^ (-ρ.re) * Real.exp (-(n : ℝ) / Y)
      ≤ (n : ℝ) * (n : ℝ) ^ (-ρ.re) * Real.exp (-(n : ℝ) / Y) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmc (Real.rpow_nonneg hnpos.le _))
          (Real.exp_nonneg _)
    _ ≤ (n : ℝ) ^ k * Real.exp (-(n : ℝ) / Y) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = (n : ℝ) ^ k * Real.exp (-(1 / Y) * (n : ℝ)) := by rw [hexp]
    _ ≤ (max 1 K : ℝ) * ((n : ℝ) ^ k * Real.exp (-(1 / Y) * (n : ℝ))) :=
        le_mul_of_one_le_left (by positivity) (le_max_left (1 : ℝ) (K : ℝ))

/-! ## The far tail as a shifted sum -/

lemma detFarTail_eq_shift (K : ℕ) (Y Z : ℝ) (ρ : ℂ) (hf : Summable (detTerm K Y ρ)) :
    detFarTail K Y Z ρ = ∑' n, detTerm K Y ρ (n + (⌊Z⌋₊ + 1)) := by
  have hg : Summable (fun n : ℕ => if ⌊Z⌋₊ < n then detTerm K Y ρ n else 0) :=
    Summable.of_norm_bounded hf.norm (fun n => by
      by_cases h : ⌊Z⌋₊ < n
      · simp only [if_pos h]
        exact le_refl _
      · simp only [if_neg h, norm_zero]
        exact norm_nonneg _)
  have h1 : (∑' i : ℕ, (if ⌊Z⌋₊ < i then detTerm K Y ρ i else 0))
      = ∑ i ∈ Finset.range (⌊Z⌋₊ + 1), (if ⌊Z⌋₊ < i then detTerm K Y ρ i else 0)
        + ∑' i : ℕ,
            (if ⌊Z⌋₊ < i + (⌊Z⌋₊ + 1) then detTerm K Y ρ (i + (⌊Z⌋₊ + 1)) else 0) :=
    (hg.sum_add_tsum_nat_add (⌊Z⌋₊ + 1)).symm
  have hzero : ∑ i ∈ Finset.range (⌊Z⌋₊ + 1),
      (if ⌊Z⌋₊ < i then detTerm K Y ρ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    exact if_neg (by omega)
  have hsh : ∀ i : ℕ, (if ⌊Z⌋₊ < i + (⌊Z⌋₊ + 1) then detTerm K Y ρ (i + (⌊Z⌋₊ + 1)) else 0)
      = detTerm K Y ρ (i + (⌊Z⌋₊ + 1)) := fun i => if_pos (by omega)
  rw [hzero, zero_add] at h1
  rw [tsum_congr hsh] at h1
  rw [detFarTail_eq_tsum]
  exact h1

/-! ## The `n = 1` term -/

lemma detTerm_one (K : ℕ) (Y : ℝ) (hK : 1 ≤ K) (ρ : ℂ) :
    detTerm K Y ρ 1 = ((Real.exp (-(1 / Y)) : ℝ) : ℂ) := by
  have hcast : (-(1 : ℂ) / Y) = (((-(1 / Y)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one]
    ring
  simp only [detTerm, mCoef_one K hK, Nat.cast_one, Complex.one_cpow, one_mul, hcast,
    ← Complex.ofReal_exp]

/-! ## The finite head of the sum equals the main term plus the truncated tail -/

lemma range_sum_detTerm (K : ℕ) (Y Z : ℝ) (hK : 1 ≤ K) (hZ : 1 ≤ Z) (ρ : ℂ) :
    ∑ n ∈ Finset.range (⌊Z⌋₊ + 1), detTerm K Y ρ n
      = detTerm K Y ρ 1 + detTail K Y Z ρ := by
  have hN : 1 ≤ ⌊Z⌋₊ := Nat.le_floor (n := 1) (by simpa using hZ)
  have hf0 : detTerm K Y ρ 0 = 0 := by simp [detTerm, mCoef]
  have hzero : ∀ n : ℕ, 2 ≤ n → n ≤ K → detTerm K Y ρ n = 0 := by
    intro n hn2 hnK
    simp only [detTerm]
    rw [mCoef_eq_zero hn2 hnK, zero_mul, zero_mul]
  have hsplit : ∑ n ∈ Finset.range (⌊Z⌋₊ + 1), detTerm K Y ρ n
      = ∑ x ∈ Finset.range 2, detTerm K Y ρ x
        + ∑ x ∈ Finset.range (⌊Z⌋₊ - 1), detTerm K Y ρ (2 + x) := by
    have h := Finset.sum_range_add (detTerm K Y ρ) 2 (⌊Z⌋₊ - 1)
    rw [show 2 + (⌊Z⌋₊ - 1) = ⌊Z⌋₊ + 1 by omega] at h
    exact h
  have h2 : ∑ x ∈ Finset.range 2, detTerm K Y ρ x
      = detTerm K Y ρ 0 + detTerm K Y ρ 1 := by
    simp [Finset.sum_range_succ]
  have hshift : ∑ x ∈ Finset.range (⌊Z⌋₊ - 1), detTerm K Y ρ (2 + x)
      = ∑ k ∈ Finset.Ico 2 (⌊Z⌋₊ + 1), detTerm K Y ρ k := by
    rw [Finset.sum_Ico_eq_sum_range (detTerm K Y ρ) 2 (⌊Z⌋₊ + 1),
      show ⌊Z⌋₊ + 1 - 2 = ⌊Z⌋₊ - 1 by omega]
  have hsub0 : ∑ n ∈ Finset.Ioc K ⌊Z⌋₊, detTerm K Y ρ n
      = ∑ k ∈ Finset.Ico 2 (⌊Z⌋₊ + 1), detTerm K Y ρ k := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Ico]
      omega
    · intro x hx hxnot
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_Ioc] at hxnot
      have hxK : x ≤ K := by
        by_contra h
        rw [not_le] at h
        exact hxnot ⟨h, by omega⟩
      exact hzero x hx.1 hxK
  rw [detTail_eq_sum, hsplit, h2, hshift, ← hsub0, hf0]
  ring

/-! ## The split -/

/-- (Put this in namespace `Work.ZeroDensity.Ingham`, with `open scoped Classical BigOperators` and
`open MeasureTheory`; import `Submission.Work.ZeroDensity.Ingham.Defs` and
`Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs`.)

**Splitting the detector sum at the truncation point.**  For `Y > 0`, `K ≥ 1`, `Z ≥ 1` and any
`ρ`, the full smoothed sum `detSum K Y ρ = Σ_{n≥1} a_K(n) n^{-ρ} e^{-n/Y}` decomposes into the main
term `e^{-1/Y}` (from `n = 1`, since `a_K(1) = 1`), the truncated tail
`detTail K Y Z ρ = Σ_{K < n ≤ ⌊Z⌋₊} a_K(n) n^{-ρ} e^{-n/Y}` (the terms with `2 ≤ n ≤ K` vanish) and
the discarded far tail `detFarTail K Y Z ρ = Σ_{n > ⌊Z⌋₊} a_K(n) n^{-ρ} e^{-n/Y}`.

`mCoef K n` is the truncated Möbius coefficient `Σ_{d | n, d ≤ K} μ(d)`.  The elementary facts used
are in `Submission/Work/ZeroDensity/Ingham/Defs.lean`: `mCoef_zero` (`mCoef K 0 = 0`), `mCoef_one`
(`mCoef K 1 = 1`, needs `1 ≤ K`) and `mCoef_eq_zero` (`mCoef K n = 0` for `2 ≤ n ≤ K`); and the
summand is absolutely summable because `‖mCoef K n‖ ≤ (Nat.divisors n).card` (`norm_mCoef_le_tau`)
together with `(Nat.divisors n).card ≤ 2√n` and the exponential factor `e^{-n/Y}`.  Then split the
`tsum` (e.g. via `Summable.sum_add_tsum_nat_add` on the tail from `⌊Z⌋₊ + 1`, or
`tsum_eq_add_tsum_ite`), noting `1 ≤ ⌊Z⌋₊` follows from `1 ≤ Z`, so that the `n = 1` term appears in
neither `detTail` nor `detFarTail`.  The hypothesis `1 ≤ Z` is necessary: for `⌊Z⌋₊ = 0` the far tail
would also contain the `n = 1` term. -/
theorem detSumSplit (K : ℕ) (Y Z : ℝ) (hY : 0 < Y) (hK : 1 ≤ K) (hZ : 1 ≤ Z) (ρ : ℂ) :
    detSum K Y ρ = ((Real.exp (-(1 / Y)) : ℝ) : ℂ) + detTail K Y Z ρ + detFarTail K Y Z ρ := by
  have hA : Summable (detTerm K Y ρ) := detTerm_summable K Y hY ρ
  have hB := range_sum_detTerm K Y Z hK hZ ρ
  have hC := detFarTail_eq_shift K Y Z ρ hA
  have hdet1 := detTerm_one K Y hK ρ
  have hsplit := (hA.sum_add_tsum_nat_add (⌊Z⌋₊ + 1)).symm
  have hmain : detSum K Y ρ = detTerm K Y ρ 1 + detTail K Y Z ρ + detFarTail K Y Z ρ := by
    rw [detSum_eq_tsum, hsplit, hB, hC]
  rw [hmain, hdet1]

end Work.ZeroDensity.Ingham
