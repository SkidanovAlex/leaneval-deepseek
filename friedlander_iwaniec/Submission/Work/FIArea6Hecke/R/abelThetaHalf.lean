import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace Work.FIArea6Hecke.R

private lemma abelThetaBoundaryBound {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {a : ℕ → ℂ} {C : ℝ} (hC : 0 < C)
    (hA : ∀ k : ℕ, 1 ≤ k → ‖∑ j ∈ Finset.range k, a j‖ ≤ C * (k : ℝ) ^ θ)
    {s : ℂ} {N M : ℕ} (hN : 1 ≤ N) (hNM : N < M) (hσθ : θ < s.re) :
    ‖(M - 1 : ℂ) ^ (-s) * (∑ j ∈ Finset.range M, a j)‖
      + ‖(N : ℂ) ^ (-s) * (∑ j ∈ Finset.range N, a j)‖
      ≤ 3 * C * (N : ℝ) ^ (θ - s.re) := by
  have hM2 : 2 ≤ M := by omega
  have hM1 : 1 ≤ M - 1 := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hM1pos : (0 : ℝ) < ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M - 1)
  have hM1nn : (0 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := le_of_lt hM1pos
  have hcast : (M - 1 : ℂ) = ((M - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
  have hnormM : ‖(M - 1 : ℂ) ^ (-s)‖ = ((M - 1 : ℕ) : ℝ) ^ (-s.re) := by
    rw [hcast, Complex.norm_natCast_cpow_of_pos (by omega : 0 < M - 1), Complex.neg_re]
  have hnormN : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N), Complex.neg_re]
  have hMA : ‖∑ j ∈ Finset.range M, a j‖ ≤ C * (M : ℝ) ^ θ := hA M (by omega)
  have hNA : ‖∑ j ∈ Finset.range N, a j‖ ≤ C * (N : ℝ) ^ θ := hA N hN
  rw [norm_mul, norm_mul, hnormM, hnormN]
  have h2θ : (2 : ℝ) ^ θ ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hθ1
    simpa using h
  have hMcast : (M : ℝ) ≤ 2 * ((M - 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ M := by omega
    have heq : (M : ℝ) = ((M - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub h1]; norm_num
    have hge : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hM1
    linarith [heq]
  have hMpow : (M : ℝ) ^ θ ≤ (2 : ℝ) ^ θ * ((M - 1 : ℕ) : ℝ) ^ θ := by
    calc (M : ℝ) ^ θ ≤ (2 * ((M - 1 : ℕ) : ℝ)) ^ θ :=
          Real.rpow_le_rpow (Nat.cast_nonneg M) hMcast hθ0
      _ = (2 : ℝ) ^ θ * ((M - 1 : ℕ) : ℝ) ^ θ := Real.mul_rpow (by norm_num) hM1nn
  have hM1leN : (N : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : N ≤ M - 1)
  have hExpM : ((M - 1 : ℕ) : ℝ) ^ (θ - s.re) ≤ (N : ℝ) ^ (θ - s.re) :=
    Real.rpow_le_rpow_of_nonpos hNpos hM1leN (by linarith)
  have hrpM : ((M - 1 : ℕ) : ℝ) ^ (-s.re) * ((M - 1 : ℕ) : ℝ) ^ θ
      = ((M - 1 : ℕ) : ℝ) ^ (θ - s.re) := by
    rw [← Real.rpow_add hM1pos]; congr 1; ring
  have hrpN : (N : ℝ) ^ (-s.re) * (N : ℝ) ^ θ = (N : ℝ) ^ (θ - s.re) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have h1 : ((M - 1 : ℕ) : ℝ) ^ (-s.re) * ‖∑ j ∈ Finset.range M, a j‖
      ≤ 2 * C * (N : ℝ) ^ (θ - s.re) := by
    calc ((M - 1 : ℕ) : ℝ) ^ (-s.re) * ‖∑ j ∈ Finset.range M, a j‖
        ≤ ((M - 1 : ℕ) : ℝ) ^ (-s.re) * (C * (M : ℝ) ^ θ) :=
          mul_le_mul_of_nonneg_left hMA (Real.rpow_nonneg hM1nn _)
      _ ≤ ((M - 1 : ℕ) : ℝ) ^ (-s.re) * (C * ((2 : ℝ) ^ θ * ((M - 1 : ℕ) : ℝ) ^ θ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hMpow (le_of_lt hC)) (Real.rpow_nonneg hM1nn _)
      _ = C * (2 : ℝ) ^ θ * (((M - 1 : ℕ) : ℝ) ^ (-s.re) * ((M - 1 : ℕ) : ℝ) ^ θ) := by ring
      _ = C * (2 : ℝ) ^ θ * ((M - 1 : ℕ) : ℝ) ^ (θ - s.re) := by rw [hrpM]
      _ ≤ C * 2 * ((M - 1 : ℕ) : ℝ) ^ (θ - s.re) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hM1nn _)
          exact mul_le_mul_of_nonneg_left h2θ (le_of_lt hC)
      _ ≤ C * 2 * (N : ℝ) ^ (θ - s.re) := by
          apply mul_le_mul_of_nonneg_left hExpM
          exact mul_nonneg (le_of_lt hC) (by norm_num)
      _ = 2 * C * (N : ℝ) ^ (θ - s.re) := by ring
  have h2 : (N : ℝ) ^ (-s.re) * ‖∑ j ∈ Finset.range N, a j‖
      ≤ C * (N : ℝ) ^ (θ - s.re) := by
    calc (N : ℝ) ^ (-s.re) * ‖∑ j ∈ Finset.range N, a j‖
        ≤ (N : ℝ) ^ (-s.re) * (C * (N : ℝ) ^ θ) :=
          mul_le_mul_of_nonneg_left hNA (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ = C * ((N : ℝ) ^ (-s.re) * (N : ℝ) ^ θ) := by ring
      _ = C * (N : ℝ) ^ (θ - s.re) := by rw [hrpN]
  calc ((M - 1 : ℕ) : ℝ) ^ (-s.re) * ‖∑ j ∈ Finset.range M, a j‖
        + (N : ℝ) ^ (-s.re) * ‖∑ j ∈ Finset.range N, a j‖
      ≤ 2 * C * (N : ℝ) ^ (θ - s.re) + C * (N : ℝ) ^ (θ - s.re) := add_le_add h1 h2
    _ = 3 * C * (N : ℝ) ^ (θ - s.re) := by ring

private lemma cpow_sub_integral_le {s : ℂ} {n : ℕ} (hn : 1 ≤ n) (hσ : 0 < s.re) :
    ‖(n : ℂ) ^ (-s) - (((n + 1 : ℕ)) : ℂ) ^ (-s)‖
      ≤ ‖s‖ * ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), x ^ (-s.re - 1) := by
  have hn0 : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hsne : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  have hnm : (n : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by push_cast; linarith
  have hne : (-s - 1 : ℂ) ≠ -1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.sub_re, Complex.one_re] at hre
    linarith [hσ]
  have hnotin : (0 : ℝ) ∉ Set.uIcc (n : ℝ) (((n + 1 : ℕ)) : ℝ) := by
    rw [Set.uIcc_of_le hnm]
    intro hx; rw [Set.mem_Icc] at hx
    linarith [hx.1, hnpos]
  have hint : ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), (x : ℂ) ^ (-s - 1)
      = ((((n + 1 : ℕ)) : ℂ) ^ (-s) - (n : ℂ) ^ (-s)) / (-s) := by
    rw [integral_cpow (Or.inr ⟨hne, hnotin⟩)]
    rw [show (-s - 1 : ℂ) + 1 = -s by ring]
    simp only [Complex.ofReal_natCast]
  have hdiff : (n : ℂ) ^ (-s) - (((n + 1 : ℕ)) : ℂ) ^ (-s)
      = s * ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), (x : ℂ) ^ (-s - 1) := by
    rw [hint]
    field_simp
    ring
  have hnorm1 : ‖(n : ℂ) ^ (-s) - (((n + 1 : ℕ)) : ℂ) ^ (-s)‖
      = ‖s‖ * ‖∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), (x : ℂ) ^ (-s - 1)‖ := by
    rw [hdiff, norm_mul]
  have hre : (-s - 1 : ℂ).re = -s.re - 1 := by
    simp only [Complex.neg_re, Complex.sub_re, Complex.one_re]
  have hnorm2 : ‖∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), (x : ℂ) ^ (-s - 1)‖
      ≤ ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), x ^ (-s.re - 1) := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hnm) (le_of_eq ?_)
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hnm] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hnpos hx.1
    simp only []
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
  rw [hnorm1]
  exact mul_le_mul_of_nonneg_left hnorm2 (norm_nonneg s)

/-- Weighted pointwise bound with the factor `2^θ`. -/
private lemma cpow_sub_weighted_le {s : ℂ} {θ : ℝ} (hθ : 0 ≤ θ) (hσθ : θ < s.re)
    {n : ℕ} (hn : 1 ≤ n) :
    (((n + 1 : ℕ)) : ℝ) ^ θ * ‖(((n + 1 : ℕ)) : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖
      ≤ (2 : ℝ) ^ θ * ‖s‖ * ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), x ^ (θ - s.re - 1) := by
  have hσ : 0 < s.re := lt_of_le_of_lt hθ hσθ
  have hn0 : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hnm : (n : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by push_cast; linarith
  have hbase : ‖(((n + 1 : ℕ)) : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖
      = ‖(n : ℂ) ^ (-s) - (((n + 1 : ℕ)) : ℂ) ^ (-s)‖ := norm_sub_rev _ _
  have step1 : (((n + 1 : ℕ)) : ℝ) ^ θ * ‖(((n + 1 : ℕ)) : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖
      ≤ (((n + 1 : ℕ)) : ℝ) ^ θ
          * (‖s‖ * ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), x ^ (-s.re - 1)) :=
    mul_le_mul_of_nonneg_left (by rw [hbase]; exact cpow_sub_integral_le hn hσ)
      (Real.rpow_nonneg (Nat.cast_nonneg _) θ)
  have hint : ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ),
        (((n + 1 : ℕ)) : ℝ) ^ θ * x ^ (-s.re - 1)
      ≤ ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), (2 : ℝ) ^ θ * x ^ (θ - s.re - 1) := by
    apply intervalIntegral.integral_mono_on hnm
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const (f := fun x : ℝ => x) continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hnm] at hx
      exact Or.inl (ne_of_gt (lt_of_lt_of_le hnpos hx.1))
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const (f := fun x : ℝ => x) continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hnm] at hx
      exact Or.inl (ne_of_gt (lt_of_lt_of_le hnpos hx.1))
    · intro x hx
      rw [Set.mem_Icc] at hx
      have hx0 : 0 < x := lt_of_lt_of_le hnpos hx.1
      have hx2 : (((n + 1 : ℕ)) : ℝ) ≤ 2 * x := by
        have h1 : (n : ℝ) + 1 ≤ 2 * x := by
          have : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hn0) hx.1
          linarith [hx.1, this]
        push_cast at h1 ⊢
        linarith
      have hpow : (((n + 1 : ℕ)) : ℝ) ^ θ ≤ (2 * x) ^ θ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hx2 hθ
      rw [Real.mul_rpow (by norm_num) (le_of_lt hx0)] at hpow
      have h1 : (((n + 1 : ℕ)) : ℝ) ^ θ * x ^ (-s.re - 1)
          ≤ ((2 : ℝ) ^ θ * x ^ θ) * x ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (le_of_lt hx0) _)
      have h2 : ((2 : ℝ) ^ θ * x ^ θ) * x ^ (-s.re - 1) = (2 : ℝ) ^ θ * x ^ (θ - s.re - 1) := by
        have hexp : θ + (-s.re - 1) = θ - s.re - 1 := by ring
        rw [mul_assoc, ← Real.rpow_add hx0, hexp]
      exact h1.trans (le_of_eq h2)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  calc (((n + 1 : ℕ)) : ℝ) ^ θ * ‖(((n + 1 : ℕ)) : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖
      ≤ (((n + 1 : ℕ)) : ℝ) ^ θ
          * (‖s‖ * ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), x ^ (-s.re - 1)) := step1
    _ = ‖s‖ * ((((n + 1 : ℕ)) : ℝ) ^ θ
          * ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), x ^ (-s.re - 1)) := by ring
    _ ≤ ‖s‖ * ((2 : ℝ) ^ θ
          * ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), x ^ (θ - s.re - 1)) :=
        mul_le_mul_of_nonneg_left hint (norm_nonneg s)
    _ = (2 : ℝ) ^ θ * ‖s‖
          * ∫ x in (n : ℝ)..(((n + 1 : ℕ)) : ℝ), x ^ (θ - s.re - 1) := by ring

private lemma abelThetaInteriorBound {θ : ℝ} (hθ : 0 ≤ θ) {s : ℂ} (hσθ : θ < s.re)
    {N K : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Finset.Ico N K, (i + 1 : ℝ) ^ θ * ‖(i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)‖
      ≤ (2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ) := by
  have hσ : 0 < s.re := lt_of_le_of_lt hθ hσθ
  have hden : 0 < s.re - θ := sub_pos.mpr hσθ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hAnn : 0 ≤ (2 : ℝ) ^ θ * ‖s‖ :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) θ) (norm_nonneg s)
  have hRHSnn : 0 ≤ (2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ) :=
    div_nonneg (mul_nonneg hAnn (Real.rpow_nonneg (le_of_lt hNpos) _)) (le_of_lt hden)
  by_cases hNK : N ≤ K
  · have hsum1 : ∑ i ∈ Finset.Ico N K,
          (i + 1 : ℝ) ^ θ * ‖(i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)‖
        ≤ ∑ i ∈ Finset.Ico N K,
          (2 : ℝ) ^ θ * ‖s‖ * ∫ x in (i : ℝ)..(((i + 1 : ℕ)) : ℝ), x ^ (θ - s.re - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi1 : 1 ≤ i := le_trans hN hi.1
      simpa only [Nat.cast_add, Nat.cast_one] using cpow_sub_weighted_le hθ hσθ hi1
    refine hsum1.trans ?_
    rw [← Finset.mul_sum]
    have hsumint : ∑ i ∈ Finset.Ico N K,
          ∫ x in (i : ℝ)..(((i + 1 : ℕ)) : ℝ), x ^ (θ - s.re - 1)
        = ∫ x in (N : ℝ)..(K : ℝ), x ^ (θ - s.re - 1) := by
      refine intervalIntegral.sum_integral_adjacent_intervals_Ico
        (a := fun k : ℕ => (k : ℝ)) (f := fun x : ℝ => x ^ (θ - s.re - 1)) hNK ?_
      intro k hk
      rw [Set.mem_Ico] at hk
      have hk0 : 0 < k := by omega
      have hkle : (k : ℝ) ≤ (((k + 1 : ℕ)) : ℝ) := by push_cast; linarith
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.rpow_const (f := fun x : ℝ => x) continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hkle] at hx
      exact Or.inl (ne_of_gt (lt_of_lt_of_le (by exact_mod_cast hk0) hx.1))
    rw [hsumint]
    have hne2 : θ - s.re - 1 ≠ -1 := by intro hh; linarith [hσθ]
    have hnotin2 : (0 : ℝ) ∉ Set.uIcc (N : ℝ) (K : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hNK)]
      intro hx; rw [Set.mem_Icc] at hx
      linarith [hx.1, hNpos]
    rw [integral_rpow (Or.inr ⟨hne2, hnotin2⟩),
      show θ - s.re - 1 + 1 = θ - s.re by ring]
    have hKp : 0 ≤ (K : ℝ) ^ (θ - s.re) := Real.rpow_nonneg (Nat.cast_nonneg K) _
    have hkey : ((K : ℝ) ^ (θ - s.re) - (N : ℝ) ^ (θ - s.re)) / (θ - s.re)
        = ((N : ℝ) ^ (θ - s.re) - (K : ℝ) ^ (θ - s.re)) / (s.re - θ) := by
      rw [div_eq_div_iff (by linarith : θ - s.re ≠ 0) (by linarith : s.re - θ ≠ 0)]
      ring
    rw [hkey, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right
    · apply mul_le_mul_of_nonneg_left _ hAnn
      linarith
    · exact le_of_lt hden
  · have hemp : Finset.Ico N K = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    exact hRHSnn

private lemma core {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {a : ℕ → ℂ} {C : ℝ}, 0 < C →
      (∀ N : ℕ, 1 ≤ N → ‖∑ n ∈ Finset.range N, a n‖ ≤ C * (N : ℝ) ^ θ) →
      ∀ (s : ℂ) (N M : ℕ), 1 ≤ N → N ≤ M → θ < s.re →
        ‖(∑ n ∈ Finset.range M, a n / (n : ℂ) ^ s)
          - (∑ n ∈ Finset.range N, a n / (n : ℂ) ^ s)‖
          ≤ K * C * (1 + ‖s‖ / (s.re - θ)) * (N : ℝ) ^ (θ - s.re) := by
  refine ⟨3, by norm_num, ?_⟩
  intro a C hC hA s N M hN hNM hσθ
  have hden : 0 < s.re - θ := sub_pos.mpr hσθ
  have hNn : 0 ≤ (N : ℝ) ^ (θ - s.re) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hy : 0 ≤ ‖s‖ / (s.re - θ) := div_nonneg (norm_nonneg s) (le_of_lt hden)
  have h2θ : (2 : ℝ) ^ θ ≤ 3 := by
    have h1 : (2 : ℝ) ^ θ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hθ1)
    rw [Real.rpow_one] at h1
    linarith
  rcases lt_or_eq_of_le hNM with hlt | heq
  · have hNMle : N ≤ M := le_of_lt hlt
    have hMc : ((M - 1 : ℕ) : ℂ) = (M : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
    have hblock : (∑ n ∈ Finset.range M, a n / (n : ℂ) ^ s)
        - (∑ n ∈ Finset.range N, a n / (n : ℂ) ^ s)
        = ∑ n ∈ Finset.Ico N M, a n / (n : ℂ) ^ s :=
      (Finset.sum_Ico_eq_sub (fun n => a n / (n : ℂ) ^ s) hNMle).symm
    have hsum2 : ∑ n ∈ Finset.Ico N M, a n / (n : ℂ) ^ s
        = ∑ n ∈ Finset.Ico N M, a n * (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [div_eq_mul_inv, Complex.cpow_neg]
    have habel := Finset.sum_Ico_by_parts (f := fun i : ℕ => (i : ℂ) ^ (-s))
        (g := fun i : ℕ => a i) hlt
    have habel' : ∑ i ∈ Finset.Ico N M, a i * (i : ℂ) ^ (-s)
        = ((M - 1 : ℕ) : ℂ) ^ (-s) * (∑ j ∈ Finset.range M, a j)
          - (N : ℂ) ^ (-s) * (∑ j ∈ Finset.range N, a j)
          - ∑ i ∈ Finset.Ico N (M - 1),
              ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j) := by
      rw [show ∑ i ∈ Finset.Ico N M, a i * (i : ℂ) ^ (-s)
            = ∑ i ∈ Finset.Ico N M, (i : ℂ) ^ (-s) * a i from by
              apply Finset.sum_congr rfl; intro i _; rw [mul_comm]]
      simpa only [smul_eq_mul, Nat.cast_add, Nat.cast_one] using habel
    rw [hblock, hsum2, habel', hMc]
    have hbd := abelThetaBoundaryBound hθ0 (hθ1) hC hA hN hlt hσθ
    have hInt : ‖∑ i ∈ Finset.Ico N (M - 1),
          ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖
        ≤ C * ((2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ)) := by
      calc ‖∑ i ∈ Finset.Ico N (M - 1),
              ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖
          ≤ ∑ i ∈ Finset.Ico N (M - 1),
              ‖((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖ :=
            norm_sum_le _ _
        _ = ∑ i ∈ Finset.Ico N (M - 1),
              ‖(i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)‖ * ‖∑ j ∈ Finset.range (i + 1), a j‖ := by
            apply Finset.sum_congr rfl; intro i _; rw [norm_mul]
        _ ≤ ∑ i ∈ Finset.Ico N (M - 1),
              ‖(i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)‖ * (C * (i + 1 : ℝ) ^ θ) := by
            apply Finset.sum_le_sum; intro i _
            have hAi : ‖∑ j ∈ Finset.range (i + 1), a j‖ ≤ C * (i + 1 : ℝ) ^ θ := by
              have := hA (i + 1) (by omega)
              simpa only [Nat.cast_add, Nat.cast_one] using this
            exact mul_le_mul_of_nonneg_left hAi (norm_nonneg _)
        _ = C * ∑ i ∈ Finset.Ico N (M - 1),
              (i + 1 : ℝ) ^ θ * ‖(i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)‖ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i _; ring
        _ ≤ C * ((2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ)) :=
            mul_le_mul_of_nonneg_left (abelThetaInteriorBound hθ0 hσθ hN) (le_of_lt hC)
    have hfinal : 3 * C * (N : ℝ) ^ (θ - s.re)
          + C * ((2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ))
        ≤ 3 * C * (1 + ‖s‖ / (s.re - θ)) * (N : ℝ) ^ (θ - s.re) := by
      have hkey : C * ((2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ))
          ≤ 3 * C * (N : ℝ) ^ (θ - s.re) * (‖s‖ / (s.re - θ)) := by
        have hfac : 0 ≤ C * (N : ℝ) ^ (θ - s.re) * (‖s‖ / (s.re - θ)) :=
          mul_nonneg (mul_nonneg (le_of_lt hC) hNn) hy
        calc C * ((2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ))
            = (C * (N : ℝ) ^ (θ - s.re) * (‖s‖ / (s.re - θ))) * (2 : ℝ) ^ θ := by ring
          _ ≤ (C * (N : ℝ) ^ (θ - s.re) * (‖s‖ / (s.re - θ))) * 3 :=
              mul_le_mul_of_nonneg_left h2θ hfac
          _ = 3 * C * (N : ℝ) ^ (θ - s.re) * (‖s‖ / (s.re - θ)) := by ring
      calc 3 * C * (N : ℝ) ^ (θ - s.re)
            + C * ((2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ))
          ≤ 3 * C * (N : ℝ) ^ (θ - s.re)
            + 3 * C * (N : ℝ) ^ (θ - s.re) * (‖s‖ / (s.re - θ)) := add_le_add le_rfl hkey
        _ = 3 * C * (1 + ‖s‖ / (s.re - θ)) * (N : ℝ) ^ (θ - s.re) := by ring
    have htri : ‖((M : ℂ) - 1) ^ (-s) * (∑ j ∈ Finset.range M, a j)
          - (N : ℂ) ^ (-s) * (∑ j ∈ Finset.range N, a j)
          - ∑ i ∈ Finset.Ico N (M - 1),
              ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖
        ≤ (‖((M : ℂ) - 1) ^ (-s) * (∑ j ∈ Finset.range M, a j)‖
            + ‖(N : ℂ) ^ (-s) * (∑ j ∈ Finset.range N, a j)‖)
          + ‖∑ i ∈ Finset.Ico N (M - 1),
              ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖ := by
      calc _ ≤ ‖((M : ℂ) - 1) ^ (-s) * (∑ j ∈ Finset.range M, a j)
                - (N : ℂ) ^ (-s) * (∑ j ∈ Finset.range N, a j)‖
              + ‖∑ i ∈ Finset.Ico N (M - 1),
                  ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖ :=
            norm_sub_le _ _
        _ ≤ (‖((M : ℂ) - 1) ^ (-s) * (∑ j ∈ Finset.range M, a j)‖
              + ‖(N : ℂ) ^ (-s) * (∑ j ∈ Finset.range N, a j)‖)
            + ‖∑ i ∈ Finset.Ico N (M - 1),
                ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
    calc ‖((M : ℂ) - 1) ^ (-s) * (∑ j ∈ Finset.range M, a j)
          - (N : ℂ) ^ (-s) * (∑ j ∈ Finset.range N, a j)
          - ∑ i ∈ Finset.Ico N (M - 1),
              ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖
        ≤ (‖((M : ℂ) - 1) ^ (-s) * (∑ j ∈ Finset.range M, a j)‖
            + ‖(N : ℂ) ^ (-s) * (∑ j ∈ Finset.range N, a j)‖)
          + ‖∑ i ∈ Finset.Ico N (M - 1),
              ((i + 1 : ℂ) ^ (-s) - (i : ℂ) ^ (-s)) * (∑ j ∈ Finset.range (i + 1), a j)‖ := htri
      _ ≤ 3 * C * (N : ℝ) ^ (θ - s.re)
            + C * ((2 : ℝ) ^ θ * ‖s‖ * (N : ℝ) ^ (θ - s.re) / (s.re - θ)) :=
          add_le_add hbd hInt
      _ ≤ 3 * C * (1 + ‖s‖ / (s.re - θ)) * (N : ℝ) ^ (θ - s.re) := hfinal
  · rw [← heq]
    have hzero : (∑ n ∈ Finset.range N, a n / (n : ℂ) ^ s)
        - (∑ n ∈ Finset.range N, a n / (n : ℂ) ^ s) = 0 := sub_self _
    rw [hzero, norm_zero]
    have : (0 : ℝ) ≤ 3 * C * (1 + ‖s‖ / (s.re - θ)) * (N : ℝ) ^ (θ - s.re) := by
      have h1 : 0 ≤ 1 + ‖s‖ / (s.re - θ) := by linarith
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC)) h1) hNn
    exact this

theorem abelThetaHalf :
    ∃ K : ℝ, 0 < K ∧
      ∀ {a : ℕ → ℂ} {C : ℝ}, 0 < C →
        (∀ N : ℕ, 1 ≤ N → ‖∑ n ∈ Finset.range N, a n‖ ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2)) →
        ∀ (s : ℂ) (N M : ℕ), 1 ≤ N → N ≤ M → (1 : ℝ) / 2 < s.re →
          ‖(∑ n ∈ Finset.range M, a n / (n : ℂ) ^ s)
              - (∑ n ∈ Finset.range N, a n / (n : ℂ) ^ s)‖
            ≤ K * C * (1 + ‖s‖ / (s.re - 1 / 2)) * (N : ℝ) ^ ((1 : ℝ) / 2 - s.re) :=
  core (by norm_num) (by norm_num)

end Work.FIArea6Hecke.R
