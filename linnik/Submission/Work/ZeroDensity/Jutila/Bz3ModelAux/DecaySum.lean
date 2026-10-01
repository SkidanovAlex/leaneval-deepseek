import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3ModelAux.Defs

namespace Work.ZeroDensity.Jutila.Bz3ModelAux

open Finset

noncomputable section

/-! ## Auxiliary estimates for the `q`-sum of logarithmic decay factors

The main theorem `DecaySum` below bounds, uniformly in `2 ≤ z ≤ N`,

  `Σ_{q ≤ N/z} (1/q)·log(2 + ⌊N/(qz)⌋)^{−2}`.

The proof groups the terms `q ∈ [1, A]` (`A = N/z`) by the dyadic size `k = log₂(A/q)` of `A/q`.
On the block `{q : log₂(A/q) = k}` the factor `log(1 + A/q)^{−2}` is at most
`(log(1 + 2^k))^{−2} = ck k`, while `Σ_{q in block} 1/q ≤ 3` by the harmonic-number bounds; the
remaining series `Σ_k ck k` converges like `Σ_k 1/k²`.
-/

/-- The `ℚ`-valued `harmonic` numbers cast to `ℝ` are the partial sums of `∑ 1/i` over `Icc 1 n`. -/
lemma harmonic_cast_Icc (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.Icc 1 n, (1:ℝ)/(i:ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Rat.cast_inv, Rat.cast_natCast, one_div]

/-- The tail of the harmonic sum is the difference of two harmonic numbers. -/
lemma sum_Icc_succ_div_eq_harmonic (a b : ℕ) (hab : a ≤ b) :
    ∑ q ∈ Finset.Icc (a+1) b, (1:ℝ)/(q:ℝ)
      = ((harmonic b : ℚ) : ℝ) - ((harmonic a : ℚ) : ℝ) := by
  rw [harmonic_cast_Icc b, harmonic_cast_Icc a]
  have hsplit : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Icc (a+1) b := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Icc (a+1) b) := by
    rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

/-- Harmonic tail bound: for `1 ≤ a ≤ b`, `Σ_{a < q ≤ b} 1/q ≤ 1 + log b − log a`. -/
lemma sum_Icc_succ_div_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ q ∈ Finset.Icc (a+1) b, (1:ℝ)/(q:ℝ) ≤ 1 + Real.log b - Real.log a := by
  rw [sum_Icc_succ_div_eq_harmonic a b hab]
  have h1 : ((harmonic b : ℚ) : ℝ) ≤ 1 + Real.log b := harmonic_le_one_add_log b
  have h2 : Real.log (a+1) ≤ ((harmonic a : ℚ) : ℝ) := by
    have h := log_add_one_le_harmonic a
    simpa using h
  have h3 : Real.log (a:ℝ) ≤ Real.log (a+1) := by
    apply Real.log_le_log (by positivity); linarith
  linarith

/-- **Dyadic block bound.**  For every `k`, the reciprocals of the integers `q ∈ [1,A]` with
`log₂(A/q) = k` sum to at most `3`. -/
lemma fiber_sum_le (A k : ℕ) :
    ∑ q ∈ (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k), (1:ℝ)/(q:ℝ) ≤ 3 := by
  set a := A / 2^(k+1) with ha_def
  set b := A / 2^k with hb_def
  have hsubset : (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k) ⊆ Finset.Icc (a+1) b := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqA⟩, hlog⟩ := hq
    have hqpos : 0 < q := hq1
    have hAqne : A / q ≠ 0 := by
      have h1 : 1 ≤ A/q := by rw [Nat.one_le_div_iff hqpos]; exact hqA
      omega
    have h2k : 2^k ≤ A/q := by
      have h := Nat.pow_log_le_self 2 hAqne
      rwa [hlog] at h
    have h2k1 : A/q < 2^(k+1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (A/q)
      rw [hlog, Nat.succ_eq_add_one] at h
      exact h
    rw [Finset.mem_Icc]
    constructor
    · have hlt : A / 2^(k+1) < q := by
        rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(k+1)), mul_comm]
        exact (Nat.div_lt_iff_lt_mul hqpos).mp h2k1
      rw [ha_def]; omega
    · have hle : 2^k * q ≤ A := (Nat.le_div_iff_mul_le hqpos).mp h2k
      rw [hb_def, Nat.le_div_iff_mul_le (by positivity : 0 < 2^k), mul_comm]
      exact hle
  have h1 : ∑ q ∈ (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k), (1:ℝ)/(q:ℝ)
      ≤ ∑ q ∈ Finset.Icc (a+1) b, (1:ℝ)/(q:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
  refine h1.trans ?_
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have hb1 : b ≤ 1 := by
      have h0 : A / 2^(k+1) = 0 := by rw [← ha_def]; exact ha
      have hA_lt : A < 2^(k+1) := (Nat.div_eq_zero_iff_lt (by positivity : 0 < 2^(k+1))).mp h0
      have hb_lt : A / 2^k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^k)]
        calc A < 2^(k+1) := hA_lt
          _ = 2 * 2^k := by rw [pow_succ]; ring
      rw [hb_def]; omega
    calc ∑ q ∈ Finset.Icc (a+1) b, (1:ℝ)/(q:ℝ)
        = ((harmonic b : ℚ) : ℝ) := by
            rw [ha]; simp only [zero_add]; exact (harmonic_cast_Icc b).symm
      _ ≤ 1 + Real.log b := harmonic_le_one_add_log b
      _ ≤ 1 := by
          have h2 : Real.log (b:ℝ) ≤ 0 := Real.log_nonpos (by positivity) (by exact_mod_cast hb1)
          linarith
      _ ≤ 3 := by norm_num
  · have ha1 : 1 ≤ a := ha
    have hba : a ≤ b := by
      rw [ha_def, hb_def]
      exact Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)) (by positivity)
    have hle := sum_Icc_succ_div_le a b ha1 hba
    have hble : b ≤ 2*a + 1 := by
      rw [hb_def, Nat.div_le_iff_le_mul (by positivity : 0 < 2^k)]
      have hA_lt : A < (a+1) * 2^(k+1) := by
        rw [ha_def]
        exact (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(k+1))).mp (Nat.lt_succ_self _)
      have hp : (2*a+1) * 2^k + 2^k = (a+1) * 2^(k+1) := by rw [pow_succ]; ring
      have h3 := Nat.le_sub_one_of_lt hA_lt
      omega
    have hlog2 : Real.log (b:ℝ) - Real.log (a:ℝ) ≤ 2 := by
      have hapos : (0:ℝ) < a := by exact_mod_cast ha1
      have hbpos : (0:ℝ) < b := by exact_mod_cast (le_trans ha1 hba)
      rw [← Real.log_div (ne_of_gt hbpos) (ne_of_gt hapos)]
      have hratio : (b:ℝ)/(a:ℝ) ≤ 3 := by
        have hA : (b:ℝ) ≤ 2*(a:ℝ) + 1 := by exact_mod_cast hble
        have hA' : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha1
        rw [div_le_iff₀ hapos]; linarith
      calc Real.log ((b:ℝ)/(a:ℝ)) ≤ Real.log 3 := Real.log_le_log (by positivity) hratio
        _ ≤ 2 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3); linarith
    linarith

/-- `log 2 ≥ 1/2`. -/
lemma log_two_ge_half : (1:ℝ)/2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
  norm_num at h
  linarith

/-- The dyadic decay weights `ck k = (log(1 + 2^k))^{−2}`. -/
def ck (k : ℕ) : ℝ := (Real.log (1 + (2:ℝ)^k))^(-2:ℤ)

lemma ck_nonneg (k : ℕ) : 0 ≤ ck k := by
  rw [ck]; simp only [zpow_neg, zpow_ofNat]
  positivity

lemma ck_zero_le : ck 0 ≤ 4 := by
  have hgoal : (Real.log (1 + (2:ℝ)^0)^2)⁻¹ ≤ 4 := by
    have hbase : (1:ℝ) + (2:ℝ)^0 = 2 := by norm_num
    rw [hbase]
    have hhalf : (1:ℝ)/2 ≤ Real.log 2 := log_two_ge_half
    calc (Real.log 2 ^ 2)⁻¹ ≤ (((1:ℝ)/2)^2)⁻¹ :=
          inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) hhalf 2)
      _ = 4 := by norm_num
  rw [ck]; simp only [zpow_neg, zpow_ofNat]
  exact hgoal

lemma ck_succ_le (k : ℕ) : ck (k+1) ≤ 4/(k+1)^2 := by
  have hgoal : (Real.log (1 + (2:ℝ)^(k+1))^2)⁻¹ ≤ 4/(k+1)^2 := by
    have hlog : Real.log ((2:ℝ)^(k+1)) ≤ Real.log (1 + (2:ℝ)^(k+1)) := by
      apply Real.log_le_log (by positivity)
      have h : (0:ℝ) < (2:ℝ)^(k+1) := by positivity
      linarith
    have hpow : Real.log ((2:ℝ)^(k+1)) = ((k:ℝ)+1) * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    have hlow : ((k:ℝ)+1)/2 ≤ Real.log (1 + (2:ℝ)^(k+1)) := by
      have h1 : (0:ℝ) ≤ (k:ℝ)+1 := by positivity
      nlinarith [hlog, hpow, log_two_ge_half, h1]
    calc (Real.log (1 + (2:ℝ)^(k+1))^2)⁻¹ ≤ ((((k:ℝ)+1)/2)^2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hlow 2)
      _ = 4/(k+1)^2 := by
          rw [show (((k:ℝ)+1)/2)^2 = ((k:ℝ)+1)^2/4 by ring, inv_div]
  rw [ck]; simp only [zpow_neg, zpow_ofNat]
  exact hgoal

/-- `Σ_{k ≤ K} ck k` is bounded by `12`, using `Σ 1/k² ≤ 2`. -/
lemma sum_ck_le (K : ℕ) : ∑ k ∈ Finset.range (K+1), ck k ≤ 12 := by
  rw [Finset.sum_range_succ']
  have h1 : ∑ k ∈ Finset.range K, ck (k+1) ≤ 8 := by
    have hEq : ∑ k ∈ Finset.range K, (1:ℝ)/((k:ℝ)+1)^2
        = ∑ i ∈ Finset.Ico 1 (K+1), (1:ℝ)/(i:ℝ)^2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Nat.add_comm]; norm_num
    have hsub : Finset.Ico 1 (K+1) ⊆ Finset.Ioo 0 (K+1) := by
      intro i hi; simp only [Finset.mem_Ico, Finset.mem_Ioo] at hi ⊢; omega
    have h3 : ∑ i ∈ Finset.Ico 1 (K+1), (1:ℝ)/(i:ℝ)^2
        ≤ ∑ i ∈ Finset.Ioo 0 (K+1), (1:ℝ)/(i:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h4 : ∑ i ∈ Finset.Ioo 0 (K+1), (1:ℝ)/(i:ℝ)^2 ≤ 2 := by
      have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (K+1)
      simpa using h
    calc ∑ k ∈ Finset.range K, ck (k+1)
        ≤ ∑ k ∈ Finset.range K, (4:ℝ)/((k:ℝ)+1)^2 :=
          Finset.sum_le_sum (fun k _ => ck_succ_le k)
      _ = 4 * ∑ k ∈ Finset.range K, (1:ℝ)/((k:ℝ)+1)^2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ ≤ 4 * 2 := by
          gcongr
          rw [hEq]
          exact h3.trans h4
      _ = 8 := by norm_num
  have h2 : ck 0 ≤ 4 := ck_zero_le
  linarith

/-- **The `q`-sum of the logarithmic decay factors is bounded.**  There is an absolute `C > 0`
with, for all `2 ≤ z ≤ N`,

  `Σ_{q ≤ N/z} (1/q)·(log(2 + Bq z N q))^{−2} ≤ C`,  where `Bq z N q = ⌊N/(qz)⌋`
(`Submission.Work.ZeroDensity.Jutila.Bz3ModelAux.Defs`).

Route: split the range dyadically in `A/q` with `A = N/z`.  For `q ≤ A` one has `Bq z N q ≥ 1` and
`Bq z N q ≥ A/q − 1` (from `⌊N/(qz)⌋ ≥ ⌊A/q⌋ ≥ A/q − 1`), so
`log(2 + Bq z N q) ≥ log(1 + A/q) ≥ ½log(2 + A/q)`.  For the terms with `q ≤ A/4` the dyadic blocks
`q ∈ (A/2^{k+1}, A/2^k]` give `Σ_{q in block} (1/q) ≤ log 2` and `log(2 + A/q) ≥ k·log 2`, hence at
most `Σ_k log2/(k log2)^2 = O(1)`; the remaining terms `A/4 < q ≤ A` satisfy `2 + Bq ≥ 3` and
`Σ (1/q) ≤ log 4`. -/
theorem DecaySum :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N →
      (∑ q ∈ Finset.Icc 1 (N / z),
          (1 / (q : ℝ))
            * (Real.log (2 + (Work.ZeroDensity.Jutila.Bz3ModelAux.Bq z N q : ℝ))) ^ (-2 : ℤ))
        ≤ C := by
  refine ⟨40, by norm_num, ?_⟩
  intro z N hz hzN
  set A := N / z with hA_def
  have hA1 : 1 ≤ A := by
    rw [hA_def, Nat.one_le_div_iff (by omega : 0 < z)]
    exact hzN
  set K := Nat.log 2 A with hK_def
  -- Step 1: replace `Bq z N q` by `A/q` (up to the constant `2 ↔ 1` in the log).
  have hterm : ∀ q ∈ Finset.Icc 1 A,
      (1/(q:ℝ)) * (Real.log (2 + (Bq z N q : ℝ)))^(-2:ℤ)
        ≤ (1/(q:ℝ)) * (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    obtain ⟨hq1, hqA⟩ := hq
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq1
    have hq1pos : 0 < q := hq1
    have hBq_eq : Bq z N q = A / q := by
      unfold Bq
      rw [hA_def, Nat.div_div_eq_div_mul]
      congr 1
      ring
    have hbq_lt : (A:ℝ)/(q:ℝ) < ((A/q : ℕ) : ℝ) + 1 := by
      have h1 : A < (A/q + 1) * q := (Nat.div_lt_iff_lt_mul hq1pos).mp (Nat.lt_succ_self _)
      have h2 : (A:ℝ) < (((A/q : ℕ):ℝ) + 1) * (q:ℝ) := by exact_mod_cast h1
      rw [div_lt_iff₀ hqpos]
      exact h2
    have hAq1 : (1:ℝ) ≤ (A:ℝ)/q := by
      rw [le_div_iff₀ hqpos, one_mul]
      exact_mod_cast hqA
    have hlog : Real.log (1 + (A:ℝ)/q) ≤ Real.log (2 + (Bq z N q : ℝ)) := by
      apply Real.log_le_log (by linarith)
      rw [hBq_eq]
      linarith
    have hlogpos : 0 < Real.log (1 + (A:ℝ)/q) := by
      apply Real.log_pos; linarith
    have hzpow : (Real.log (2 + (Bq z N q : ℝ)))^(-2:ℤ)
        ≤ (Real.log (1 + (A:ℝ)/q))^(-2:ℤ) := by
      simp only [zpow_neg, zpow_ofNat]
      exact inv_anti₀ (pow_pos hlogpos 2) (pow_le_pow_left₀ hlogpos.le hlog 2)
    exact mul_le_mul_of_nonneg_left hzpow (by positivity)
  -- Step 2: group the terms by `k = log₂(A/q)`.
  have hmap : ∀ q ∈ Finset.Icc 1 A, Nat.log 2 (A/q) ∈ Finset.range (K+1) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mem_range]
    calc Nat.log 2 (A/q) ≤ Nat.log 2 A := Nat.log_mono_right (Nat.div_le_self A q)
      _ = K := hK_def.symm
      _ < K + 1 := Nat.lt_succ_self K
  have hfiber := Finset.sum_fiberwise_of_maps_to (s := Finset.Icc 1 A) (t := Finset.range (K+1))
    (g := fun q => Nat.log 2 (A/q)) hmap
    (fun q => (1/(q:ℝ)) * (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ))
  -- Step 3: bound each block.
  have hblock : ∀ k ∈ Finset.range (K+1),
      ∑ q ∈ (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k),
        (1/(q:ℝ)) * (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ) ≤ ck k * 3 := by
    intro k _
    have hblk : ∀ q ∈ (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k),
        (1/(q:ℝ)) * (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ) ≤ ck k * (1/(q:ℝ)) := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_Icc] at hq
      obtain ⟨⟨hq1, hqA⟩, hlogq⟩ := hq
      have hq1pos : 0 < q := hq1
      have hAqne : A / q ≠ 0 := by
        have h1 : 1 ≤ A/q := by rw [Nat.one_le_div_iff hq1pos]; exact hqA
        omega
      have h2k : 2^k ≤ A/q := by
        have h := Nat.pow_log_le_self 2 hAqne
        rwa [hlogq] at h
      have hcast : ((2:ℝ)^k) ≤ (A:ℝ)/(q:ℝ) := by
        have hc1 : ((2:ℕ)^k : ℝ) ≤ ((A/q : ℕ) : ℝ) := by exact_mod_cast h2k
        have hc2 : ((A/q : ℕ) : ℝ) ≤ (A:ℝ)/(q:ℝ) := Nat.cast_div_le
        have h := hc1.trans hc2
        simpa using h
      have hle : 1 + (2:ℝ)^k ≤ 1 + (A:ℝ)/(q:ℝ) := by linarith
      have hlog2 : Real.log (1 + (2:ℝ)^k) ≤ Real.log (1 + (A:ℝ)/(q:ℝ)) :=
        Real.log_le_log (by positivity) hle
      have hpos : 0 < Real.log (1 + (2:ℝ)^k) := by
        apply Real.log_pos
        have : (0:ℝ) < (2:ℝ)^k := by positivity
        linarith
      have hck : (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ) ≤ ck k := by
        rw [ck]; simp only [zpow_neg, zpow_ofNat]
        exact inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hlog2 2)
      calc (1/(q:ℝ)) * (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ)
          ≤ (1/(q:ℝ)) * ck k := mul_le_mul_of_nonneg_left hck (by positivity)
        _ = ck k * (1/(q:ℝ)) := by ring
    calc ∑ q ∈ (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k),
          (1/(q:ℝ)) * (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ)
        ≤ ∑ q ∈ (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k), ck k * (1/(q:ℝ)) :=
          Finset.sum_le_sum hblk
      _ = ck k * ∑ q ∈ (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k), (1/(q:ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ ck k * 3 := mul_le_mul_of_nonneg_left (fiber_sum_le A k) (ck_nonneg k)
  calc ∑ q ∈ Finset.Icc 1 A, (1/(q:ℝ)) * (Real.log (2 + (Bq z N q : ℝ)))^(-2:ℤ)
      ≤ ∑ q ∈ Finset.Icc 1 A, (1/(q:ℝ)) * (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ) :=
        Finset.sum_le_sum hterm
    _ = ∑ k ∈ Finset.range (K+1), ∑ q ∈ (Finset.Icc 1 A).filter (fun q => Nat.log 2 (A/q) = k),
          (1/(q:ℝ)) * (Real.log (1 + (A:ℝ)/(q:ℝ)))^(-2:ℤ) := hfiber.symm
    _ ≤ ∑ k ∈ Finset.range (K+1), ck k * 3 := Finset.sum_le_sum hblock
    _ = 3 * ∑ k ∈ Finset.range (K+1), ck k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ 3 * 12 := by linarith [sum_ck_le K]
    _ ≤ 40 := by norm_num

end

end Work.ZeroDensity.Jutila.Bz3ModelAux
