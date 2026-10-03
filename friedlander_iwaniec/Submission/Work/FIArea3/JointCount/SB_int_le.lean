import Mathlib
import Submission.Work.FIArea3.JointCount.tauDefs

namespace Work.FIArea3.JointCount

open Finset

/-! ## Elementary estimates for the exponential / logarithmic constants -/

lemma log_le_div_exp (y : ℝ) (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h : Real.log (y / Real.exp 1) ≤ y / Real.exp 1 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hy) (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

lemma log_one_div_log_two_le : Real.log (1 / Real.log 2) ≤ 2/5 := by
  have hα : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.log_le_iff_le_exp (one_div_pos.mpr hα)]
  have h1 : 1 / Real.log 2 ≤ 1.4641 := by
    rw [div_le_iff₀ hα]
    nlinarith [Real.log_two_gt_d9]
  have h2 : (1.4641:ℝ) ≤ Real.exp (2/5) := by
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)/5) 5
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hs
    norm_num at hs ⊢
    linarith
  linarith

lemma inv_log_two_mul_exp_one_le : 1 / (Real.log 2 * Real.exp 1) ≤ 0.5309 := by
  rw [div_le_iff₀ (mul_pos (Real.log_pos (by norm_num)) (Real.exp_pos 1))]
  have h1 : (0.6931471803:ℝ) * 2.7182818283 ≤ Real.log 2 * Real.exp 1 :=
    mul_le_mul (le_of_lt Real.log_two_gt_d9) (le_of_lt Real.exp_one_gt_d9)
      (by norm_num) (le_of_lt (Real.log_pos (by norm_num)))
  norm_num at h1
  linarith

lemma CB_le : Real.log (2 / Real.log 2) - 1 + Real.log 2 / 2 ≤ 0.44 := by
  have hα : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log (2 / Real.log 2) = Real.log 2 + Real.log (1 / Real.log 2) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hα), log_one_div]
    ring
  rw [hdiv]
  linarith [log_one_div_log_two_le, Real.log_two_lt_d9]

lemma log_four_le : Real.log 4 ≤ 1.4 := by
  rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_lt_d9]

lemma exp_two_ge_seven : (7:ℝ) ≤ Real.exp 2 := by
  have h : Real.exp 2 = (Real.exp 1)^2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have he : (2.7182818283:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
  nlinarith [he, Real.exp_pos 1]

lemma log_le_two_of_le_seven {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ 7) : Real.log (m:ℝ) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hm : (m:ℝ) ≤ 7 := by exact_mod_cast h2
  linarith [exp_two_ge_seven]

lemma exp_nat_ge (n : ℕ) : (2.7182818283:ℝ)^n ≤ Real.exp (n:ℝ) := by
  have h : Real.exp (n:ℝ) = (Real.exp 1)^n := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) n

lemma exp_nat_ge_two_mul (n : ℕ) : (2:ℝ)^n * (1.359:ℝ)^n ≤ Real.exp (n:ℝ) := by
  have h : Real.exp (n:ℝ) = (Real.exp 1)^n := by rw [← Real.exp_nat_mul]; norm_num
  rw [h, ← mul_pow]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) n

/-! ## The weighted geometric-sum bound -/

lemma SH_bound (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Finset.range K, (2:ℝ)^k / ((k:ℝ)+1) ≤ (2/3) * (2:ℝ)^(K+1) / K := by
  have hstep : ∀ K : ℕ, 4 ≤ K →
      (∑ k ∈ Finset.range K, (2:ℝ)^k / ((k:ℝ)+1) ≤ (2/3) * (2:ℝ)^(K+1) / K) →
      (∑ k ∈ Finset.range (K+1), (2:ℝ)^k / ((k:ℝ)+1) ≤
        (2/3) * (2:ℝ)^((K+1)+1) / ((K+1 : ℕ) : ℝ)) := by
    intro K hK ih
    push_cast
    have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hK1pos : (0:ℝ) < (K:ℝ)+1 := by linarith
    have hs : ∑ k ∈ Finset.range (K+1), (2:ℝ)^k / ((k:ℝ)+1)
        = ∑ k ∈ Finset.range K, (2:ℝ)^k / ((k:ℝ)+1) + (2:ℝ)^K / ((K:ℝ)+1) := by
      rw [Finset.sum_range_succ]
    rw [hs]
    have hkey : (2/3:ℝ)/(K:ℝ) + (1/2)/((K:ℝ)+1) ≤ (4/3:ℝ)/((K:ℝ)+1) := by
      have h1 : (2/3:ℝ)/(K:ℝ) ≤ (5/6:ℝ)/((K:ℝ)+1) := by
        rw [div_le_div_iff₀ hKpos hK1pos]
        have h4 : (4:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
        linarith
      have h2 : (5/6:ℝ)/((K:ℝ)+1) + (1/2)/((K:ℝ)+1) = (4/3:ℝ)/((K:ℝ)+1) := by
        field_simp
        ring
      linarith [h1, le_of_eq h2.symm]
    have hmul := mul_le_mul_of_nonneg_left hkey
      (le_of_lt (show (0:ℝ) < (2:ℝ)^(K+1) by positivity))
    have e1 : (2:ℝ)^(K+1) * ((2/3:ℝ)/(K:ℝ) + (1/2)/((K:ℝ)+1))
        = (2/3:ℝ)*(2:ℝ)^(K+1)/(K:ℝ) + (2:ℝ)^K/((K:ℝ)+1) := by
      have h2K : (2:ℝ)^K = (2:ℝ)^(K+1)/2 := by rw [pow_succ]; ring
      rw [h2K]
      field_simp
    have e2 : (2:ℝ)^(K+1) * ((4/3:ℝ)/((K:ℝ)+1))
        = (2/3:ℝ)*(2:ℝ)^((K+1)+1)/((K:ℝ)+1) := by
      have h2K : (2:ℝ)^((K+1)+1) = 2 * (2:ℝ)^(K+1) := by rw [pow_succ]; ring
      rw [h2K]
      field_simp
      ring
    rw [e1, e2] at hmul
    linarith
  have hP : ∀ n : ℕ, 4 ≤ n →
      ∑ k ∈ Finset.range n, (2:ℝ)^k / ((k:ℝ)+1) ≤ (2/3) * (2:ℝ)^(n+1) / n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num [Finset.sum_range_succ]
    | succ n hn ih => exact hstep n hn ih
  rcases (by omega : K = 1 ∨ K = 2 ∨ K = 3 ∨ 4 ≤ K) with h | h | h | h
  · subst h; norm_num [Finset.sum_range_succ]
  · subst h; norm_num [Finset.sum_range_succ]
  · subst h; norm_num [Finset.sum_range_succ]
  · exact hP K h

/-! ## The two regional estimates -/

/-- The `k`-th summand of `SBtau`. -/
noncomputable def sbTerm (n k : ℕ) : ℝ := cweight k * Bval ((k:ℝ) * Real.log 2 / (n:ℝ))

lemma sum_range_two_pow (K : ℕ) : ∑ k ∈ Finset.range K, (2:ℝ)^k = (2:ℝ)^K - 1 := by
  have h := geom_sum_eq (show (2:ℝ) ≠ 1 by norm_num) K
  rw [h]; ring

/-- `Bval x ≤ log (2/log 2) - 1 + log 2/2` for `x ≥ log 2/2`. -/
lemma Bval_le_CB {x : ℝ} (hx : Real.log 2 / 2 ≤ x) :
    Bval x ≤ Real.log (2 / Real.log 2) - 1 + Real.log 2 / 2 := by
  have hα2 : (0:ℝ) < Real.log 2/2 := by positivity
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le hα2 hx
  have hmono := Bval_antitoneOn hα2 hxpos hx
  have hval : Bval (Real.log 2/2) = Real.log (2/Real.log 2) - 1 + Real.log 2/2 := by
    rw [Bval, if_pos (by linarith [Real.log_two_lt_d9])]
    have h2 : (1:ℝ)/(Real.log 2/2) = 2/Real.log 2 := by field_simp
    rw [h2]
  linarith [hmono, le_of_eq hval]

/-- `2*(n/2) ≤ n` in `ℝ`. -/
lemma two_mul_div_two_cast_le (n : ℕ) : ((n/2 : ℕ) : ℝ) ≤ (n:ℝ)/2 := by
  have h4 : ((2*(n/2) : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 2*(n/2) ≤ n)
  push_cast at h4; linarith

/-- The logarithm bound used on the range `k ≤ n/2`. -/
noncomputable def gA (n j : ℕ) : ℝ := Real.log ((n:ℝ)/((j:ℝ)*Real.log 2)) - 1/2

lemma gA_succ (n k : ℕ) : gA n (k+1) = Real.log ((n:ℝ)/(((k:ℝ)+1)*Real.log 2)) - 1/2 := by
  rw [gA]; push_cast; ring_nf

lemma gA_one (n : ℕ) : gA n 1 = Real.log ((n:ℝ)/Real.log 2) - 1/2 := by
  rw [gA]; norm_num

/-- Pointwise bound on the "small `k`" part of `SBtau n`. -/
lemma sbTerm_A_le (n : ℕ) (hn : 4 ≤ n) {k : ℕ} (hk : k + 1 ≤ n/2) :
    sbTerm n (k+1) ≤ (2:ℝ)^k * gA n (k+1) + (if k = 0 then gA n (k+1) else 0) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hk1le : ((k:ℝ)+1) ≤ (n:ℝ)/2 := by
    have h1 : ((k+1 : ℕ):ℝ) ≤ ((n/2 : ℕ):ℝ) := by exact_mod_cast hk
    push_cast at h1
    linarith [two_mul_div_two_cast_le n]
  have hjle : ((k:ℝ)+1)*Real.log 2/(n:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hnpos]
    nlinarith [hk1le, Real.log_two_lt_d9]
  have hBval : Bval (((k:ℝ)+1)*Real.log 2/(n:ℝ))
      = Real.log ((n:ℝ)/(((k:ℝ)+1)*Real.log 2)) - 1 + ((k:ℝ)+1)*Real.log 2/(n:ℝ) := by
    rw [Bval, if_pos hjle]
    have h2 : (1:ℝ)/(((k:ℝ)+1)*Real.log 2/(n:ℝ)) = (n:ℝ)/(((k:ℝ)+1)*Real.log 2) := by
      field_simp
    rw [h2]
  have hB : Bval (((k:ℝ)+1)*Real.log 2/(n:ℝ)) ≤ gA n (k+1) := by
    rw [hBval, gA_succ]; linarith
  have hg : 0 ≤ gA n (k+1) := by
    rw [gA_succ]
    have h2 : (2:ℝ) ≤ (n:ℝ)/(((k:ℝ)+1)*Real.log 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hk1le, Real.log_two_lt_d9]
    have h3 := Real.log_le_log (by norm_num : (0:ℝ) < 2) h2
    linarith [Real.log_two_gt_d9]
  have hcw : cweight (k+1) = (2:ℝ)^k + (if k = 0 then 1 else 0) := by
    by_cases hk0 : k = 0
    · subst hk0; norm_num [cweight]
    · rw [cweight, if_neg (by omega : ¬ (k+1 = 0)), if_neg (by omega : ¬ (k+1 = 1)),
        if_neg hk0, show k+1-1 = k by omega]
      ring
  have hcwpos : 0 ≤ cweight (k+1) := by rw [hcw]; split_ifs <;> positivity
  have hrearr : ((2:ℝ)^k + (if k = 0 then 1 else 0)) * gA n (k+1)
      = (2:ℝ)^k * gA n (k+1) + (if k = 0 then gA n (k+1) else 0) := by
    by_cases hk0 : k = 0
    · subst hk0; first | (norm_num; ring) | norm_num
    · rw [if_neg hk0, if_neg hk0]; ring
  calc sbTerm n (k+1)
      = cweight (k+1) * Bval (((k:ℝ)+1)*Real.log 2/(n:ℝ)) := by
        rw [sbTerm]; push_cast; rfl
    _ ≤ cweight (k+1) * gA n (k+1) := mul_le_mul_of_nonneg_left hB hcwpos
    _ ≤ ((2:ℝ)^k + (if k = 0 then 1 else 0)) * gA n (k+1) :=
        mul_le_mul_of_nonneg_right (le_of_eq hcw) hg
    _ = (2:ℝ)^k * gA n (k+1) + (if k = 0 then gA n (k+1) else 0) := hrearr

/-- Estimate of the sum of the terms with `k ≤ n/2`. -/
lemma regionA_le (n : ℕ) (hn : 4 ≤ n) :
    ∑ k ∈ Finset.range (n/2 + 1), sbTerm n k ≤
      ((n:ℝ)/(Real.log 2 * Real.exp 1)) * (∑ k ∈ Finset.range (n/2), (2:ℝ)^k/((k:ℝ)+1))
      - (1/2)*((2:ℝ)^(n/2) - 1) + gA n 1 := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hKmem : 0 ∈ Finset.range (n/2) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_range_succ']
  have hf0 : sbTerm n 0 = 0 := by simp [sbTerm, cweight]
  rw [hf0, add_zero]
  calc ∑ k ∈ Finset.range (n/2), sbTerm n (k+1)
      ≤ ∑ k ∈ Finset.range (n/2), ((2:ℝ)^k * gA n (k+1)
          + (if k = 0 then gA n (k+1) else 0)) :=
        Finset.sum_le_sum (fun k hk => sbTerm_A_le n hn (by have := Finset.mem_range.mp hk; omega))
    _ = ∑ k ∈ Finset.range (n/2), (2:ℝ)^k * gA n (k+1) + gA n 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hKmem, Nat.zero_add]
    _ ≤ ∑ k ∈ Finset.range (n/2), (2:ℝ)^k * ((n:ℝ)/(((k:ℝ)+1)*Real.log 2*Real.exp 1) - 1/2)
          + gA n 1 := by
        apply add_le_add_left
        apply Finset.sum_le_sum
        intro k hk
        rw [gA_succ]
        have hy : 0 < (n:ℝ)/(((k:ℝ)+1)*Real.log 2) := by positivity
        have h := log_le_div_exp _ hy
        have h2 : (n:ℝ)/(((k:ℝ)+1)*Real.log 2)/Real.exp 1
            = (n:ℝ)/(((k:ℝ)+1)*Real.log 2*Real.exp 1) := by field_simp
        rw [h2] at h
        have h2k : (0:ℝ) ≤ (2:ℝ)^k := by positivity
        nlinarith [h, h2k]
    _ = ((n:ℝ)/(Real.log 2 * Real.exp 1)) * (∑ k ∈ Finset.range (n/2), (2:ℝ)^k/((k:ℝ)+1))
          - (1/2)*((2:ℝ)^(n/2) - 1) + gA n 1 := by
        have h1 : ∀ k : ℕ, (2:ℝ)^k * ((n:ℝ)/(((k:ℝ)+1)*Real.log 2*Real.exp 1) - 1/2)
            = ((n:ℝ)/(Real.log 2*Real.exp 1)) * ((2:ℝ)^k/((k:ℝ)+1)) - (1/2)*(2:ℝ)^k := by
          intro k
          have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
          have hαe : Real.log 2 * Real.exp 1 ≠ 0 := by positivity
          field_simp
        rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, sum_range_two_pow]

/-- Estimate of the sum of the terms with `k > n/2`. -/
lemma regionB_le (n : ℕ) (hn : 4 ≤ n) :
    ∑ k ∈ Finset.Ico (n/2 + 1) n, sbTerm n k ≤
      (Real.log (2 / Real.log 2) - 1 + Real.log 2 / 2) * ((2:ℝ)^(n-1) - (2:ℝ)^(n/2)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [Finset.sum_Ico_eq_sum_range]
  set M := n - (n/2 + 1) with hM
  have hpoint : ∀ k ∈ Finset.range M,
      sbTerm n ((n/2+1) + k) ≤ (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * (2:ℝ)^(n/2 + k) := by
    intro k hk
    have hjge : (n:ℝ)/2 ≤ ((n/2+1+k : ℕ):ℝ) := by
      have h2 : n + 1 ≤ 2*(n/2+1) := by omega
      have h3 : ((n+1:ℕ):ℝ) ≤ 2*((n/2+1 : ℕ):ℝ) := by exact_mod_cast h2
      have h4 : ((n/2 : ℕ):ℝ) + 1 ≤ ((n/2+1+k : ℕ):ℝ) := by
        have h5 : n/2 + 1 ≤ n/2+1+k := by omega
        exact_mod_cast h5
      push_cast at h3
      linarith
    have hx : Real.log 2/2 ≤ ((n/2+1+k : ℕ):ℝ) * Real.log 2/(n:ℝ) := by
      rw [le_div_iff₀ hnpos]
      nlinarith [hjge, Real.log_two_gt_d9]
    have hB := Bval_le_CB hx
    have hcw : cweight (n/2+1+k) = (2:ℝ)^(n/2+k) := by
      rw [cweight, if_neg (by omega : ¬ (n/2+1+k = 0)), if_neg (by omega : ¬ (n/2+1+k = 1))]
      congr 1
      omega
    rw [sbTerm, hcw]
    have h2k : (0:ℝ) ≤ (2:ℝ)^(n/2+k) := by positivity
    calc (2:ℝ)^(n/2+k) * Bval (((n/2+1+k : ℕ):ℝ) * Real.log 2/(n:ℝ))
        ≤ (2:ℝ)^(n/2+k) * (Real.log (2/Real.log 2) - 1 + Real.log 2/2) :=
          mul_le_mul_of_nonneg_left hB h2k
      _ = (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * (2:ℝ)^(n/2+k) := by ring
  calc ∑ k ∈ Finset.range M, sbTerm n ((n/2+1) + k)
      ≤ ∑ k ∈ Finset.range M, (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * (2:ℝ)^(n/2 + k) :=
        Finset.sum_le_sum hpoint
    _ = (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * ((2:ℝ)^(n-1) - (2:ℝ)^(n/2)) := by
        have h1 : (2:ℝ)^(n/2) * (2:ℝ)^(n - (n/2+1)) = (2:ℝ)^(n-1) := by
          rw [← pow_add]; congr 1; omega
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_congr rfl (fun k _ => pow_add (2:ℝ) (n/2) k), ← Finset.mul_sum,
          sum_range_two_pow, hM, mul_sub, mul_one, h1]

/-- The main structural bound on `SBtau n`. -/
lemma SBtau_le_main (n : ℕ) (hn : 4 ≤ n) :
    SBtau (n:ℝ) ≤
      ((n:ℝ)/(Real.log 2 * Real.exp 1)) * (∑ k ∈ Finset.range (n/2), (2:ℝ)^k/((k:ℝ)+1))
      - (1/2)*((2:ℝ)^(n/2) - 1) + gA n 1
      + (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * ((2:ℝ)^(n-1) - (2:ℝ)^(n/2)) := by
  have hn0 : n ≠ 0 := by omega
  have hKle : n/2 + 1 ≤ n := by omega
  have hSB : SBtau (n:ℝ) = ∑ k ∈ Finset.range (n+1), sbTerm n k := by
    rw [SBtau, Nat.ceil_natCast]; rfl
  rw [hSB, Finset.sum_range_succ]
  have hfn : sbTerm n n = 0 := by
    rw [sbTerm]
    have h1 : (n:ℝ) * Real.log 2 / (n:ℝ) = Real.log 2 := by
      field_simp
    rw [h1, Bval_eq_zero (le_refl _), mul_zero]
  rw [hfn, add_zero]
  have hsplit := Finset.sum_range_add_sum_Ico (f := sbTerm n) hKle
  rw [← hsplit]
  linarith [regionA_le n hn, regionB_le n hn]

/-- `gA n 1 = log (n/log 2) - 1/2`. -/
lemma gA_one_eq (n : ℕ) : gA n 1 = Real.log ((n:ℝ)/Real.log 2) - 1/2 := gA_one n

/-- `log (n/log 2) - 1/2 = log n + log (1/log 2) - 1/2`. -/
lemma log_div_log_two (n : ℕ) (hn : n ≠ 0) :
    Real.log ((n:ℝ)/Real.log 2) = Real.log (n:ℝ) + Real.log (1/Real.log 2) := by
  rw [Real.log_div (by positivity) (ne_of_gt (Real.log_pos (by norm_num))), log_one_div]
  ring

lemma pow_1359_quad (n : ℕ) (hn : 8 ≤ n) :
    (0.32*(n:ℝ) + 0.0015*(n:ℝ)^2) ≤ 0.5*(1.359:ℝ)^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hstep : 0.32*((n:ℝ)+1) + 0.0015*((n:ℝ)+1)^2
        ≤ 1.359*(0.32*(n:ℝ) + 0.0015*(n:ℝ)^2) := by
      have hn8 : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      nlinarith
    have h2 : (0.5:ℝ)*(1.359:ℝ)^(n+1) = 1.359 * (0.5*(1.359:ℝ)^n) := by
      rw [pow_succ]; ring
    rw [h2]
    push_cast
    linarith [ih, hstep]

theorem SB_int_le (n : ℕ) (hn : 4 ≤ n) :
    Work.FIArea3.JointCount.SBtau n ≤ 0.5 * Real.exp n / n := by
  have hmain := SBtau_le_main n hn
  rcases lt_or_ge n 8 with hn7 | hn8
  · interval_cases n
    · -- n = 4
      have hSH : (∑ k ∈ Finset.range (4/2), (2:ℝ)^k/((k:ℝ)+1)) = 2 := by
        norm_num [Finset.sum_range_succ]
      have hb := hmain
      rw [hSH] at hb
      have hp1 : ((4:ℝ)/(Real.log 2 * Real.exp 1)) * 2 ≤ 4.2472 := by
        have h2 : ((4:ℝ)/(Real.log 2 * Real.exp 1)) * 2
            = 8 * (1/(Real.log 2 * Real.exp 1)) := by ring
        rw [h2]
        calc 8 * (1/(Real.log 2 * Real.exp 1)) ≤ 8 * 0.5309 :=
              mul_le_mul_of_nonneg_left inv_log_two_mul_exp_one_le (by norm_num)
          _ = 4.2472 := by norm_num
      have hneg : -(1/2)*((2:ℝ)^(4/2) - 1) = -1.5 := by norm_num
      have hp3 : gA 4 1 ≤ 1.3 := by
        have h4 : Real.log (4:ℝ) ≤ 1.4 := log_four_le
        have h3 : Real.log (1/Real.log 2) ≤ (2:ℝ)/5 := log_one_div_log_two_le
        have hsum : Real.log (4:ℝ) + Real.log (1/Real.log 2) ≤ 1.4 + 2/5 := add_le_add h4 h3
        rw [gA_one_eq, log_div_log_two 4 (by norm_num)]
        linarith [hsum]
      have hp4 : (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * ((2:ℝ)^(4-1) - (2:ℝ)^(4/2)) ≤ 1.76 := by
        have h4 : (2:ℝ)^(4-1) - (2:ℝ)^(4/2) = 4 := by norm_num
        rw [h4]
        have := mul_le_mul_of_nonneg_right CB_le (by norm_num : (0:ℝ) ≤ 4)
        linarith [this]
      have ht : (5.8072:ℝ) ≤ 0.5 * Real.exp 4 / 4 := by
        have h1 : (46.4576:ℝ) ≤ (2.7182818283:ℝ)^4 := by norm_num
        have h2 := exp_nat_ge 4
        linarith [h1, h2]
      linarith [hb, hp1, hneg, hp3, hp4, ht]
    · -- n = 5
      have hSH : (∑ k ∈ Finset.range (5/2), (2:ℝ)^k/((k:ℝ)+1)) = 2 := by
        norm_num [Finset.sum_range_succ]
      have hb := hmain
      rw [hSH] at hb
      have hp1 : ((5:ℝ)/(Real.log 2 * Real.exp 1)) * 2 ≤ 5.309 := by
        have h2 : ((5:ℝ)/(Real.log 2 * Real.exp 1)) * 2
            = 10 * (1/(Real.log 2 * Real.exp 1)) := by ring
        rw [h2]
        calc 10 * (1/(Real.log 2 * Real.exp 1)) ≤ 10 * 0.5309 :=
              mul_le_mul_of_nonneg_left inv_log_two_mul_exp_one_le (by norm_num)
          _ = 5.309 := by norm_num
      have hneg : -(1/2)*((2:ℝ)^(5/2) - 1) = -1.5 := by norm_num
      have hp3 : gA 5 1 ≤ 1.9 := by
        have h5 : Real.log (5:ℝ) ≤ 2 := log_le_two_of_le_seven (m := 5) (by norm_num) (by norm_num)
        have h3 : Real.log (1/Real.log 2) ≤ (2:ℝ)/5 := log_one_div_log_two_le
        have hsum : Real.log (5:ℝ) + Real.log (1/Real.log 2) ≤ 2 + 2/5 := add_le_add h5 h3
        rw [gA_one_eq, log_div_log_two 5 (by norm_num)]
        linarith [hsum]
      have hp4 : (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * ((2:ℝ)^(5-1) - (2:ℝ)^(5/2)) ≤ 5.28 := by
        have h4 : (2:ℝ)^(5-1) - (2:ℝ)^(5/2) = 12 := by norm_num
        rw [h4]
        have := mul_le_mul_of_nonneg_right CB_le (by norm_num : (0:ℝ) ≤ 12)
        linarith [this]
      have ht : (10.989:ℝ) ≤ 0.5 * Real.exp 5 / 5 := by
        have h1 : (109.89:ℝ) ≤ (2.7182818283:ℝ)^5 := by norm_num
        have h2 := exp_nat_ge 5
        linarith [h1, h2]
      linarith [hb, hp1, hneg, hp3, hp4, ht]
    · -- n = 6
      have hSH : (∑ k ∈ Finset.range (6/2), (2:ℝ)^k/((k:ℝ)+1)) = 10/3 := by
        norm_num [Finset.sum_range_succ]
      have hb := hmain
      rw [hSH] at hb
      have hp1 : ((6:ℝ)/(Real.log 2 * Real.exp 1)) * (10/3) ≤ 10.618 := by
        have h2 : ((6:ℝ)/(Real.log 2 * Real.exp 1)) * (10/3)
            = 20 * (1/(Real.log 2 * Real.exp 1)) := by ring
        rw [h2]
        calc 20 * (1/(Real.log 2 * Real.exp 1)) ≤ 20 * 0.5309 :=
              mul_le_mul_of_nonneg_left inv_log_two_mul_exp_one_le (by norm_num)
          _ = 10.618 := by norm_num
      have hneg : -(1/2)*((2:ℝ)^(6/2) - 1) = -3.5 := by norm_num
      have hp3 : gA 6 1 ≤ 1.9 := by
        have h5 : Real.log (6:ℝ) ≤ 2 := log_le_two_of_le_seven (m := 6) (by norm_num) (by norm_num)
        have h3 : Real.log (1/Real.log 2) ≤ (2:ℝ)/5 := log_one_div_log_two_le
        have hsum : Real.log (6:ℝ) + Real.log (1/Real.log 2) ≤ 2 + 2/5 := add_le_add h5 h3
        rw [gA_one_eq, log_div_log_two 6 (by norm_num)]
        linarith [hsum]
      have hp4 : (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * ((2:ℝ)^(6-1) - (2:ℝ)^(6/2)) ≤ 10.56 := by
        have h4 : (2:ℝ)^(6-1) - (2:ℝ)^(6/2) = 24 := by norm_num
        rw [h4]
        have := mul_le_mul_of_nonneg_right CB_le (by norm_num : (0:ℝ) ≤ 24)
        linarith [this]
      have ht : (19.578:ℝ) ≤ 0.5 * Real.exp 6 / 6 := by
        have h1 : (234.936:ℝ) ≤ (2.7182818283:ℝ)^6 := by norm_num
        have h2 := exp_nat_ge 6
        linarith [h1, h2]
      linarith [hb, hp1, hneg, hp3, hp4, ht]
    · -- n = 7
      have hSH : (∑ k ∈ Finset.range (7/2), (2:ℝ)^k/((k:ℝ)+1)) = 10/3 := by
        norm_num [Finset.sum_range_succ]
      have hb := hmain
      rw [hSH] at hb
      have hp1 : ((7:ℝ)/(Real.log 2 * Real.exp 1)) * (10/3) ≤ 12.388 := by
        have h2 : ((7:ℝ)/(Real.log 2 * Real.exp 1)) * (10/3)
            = (70/3) * (1/(Real.log 2 * Real.exp 1)) := by ring
        rw [h2]
        calc (70/3) * (1/(Real.log 2 * Real.exp 1)) ≤ (70/3) * 0.5309 :=
              mul_le_mul_of_nonneg_left inv_log_two_mul_exp_one_le (by norm_num)
          _ ≤ 12.388 := by norm_num
      have hneg : -(1/2)*((2:ℝ)^(7/2) - 1) = -3.5 := by norm_num
      have hp3 : gA 7 1 ≤ 1.9 := by
        have h5 : Real.log (7:ℝ) ≤ 2 := log_le_two_of_le_seven (m := 7) (by norm_num) (by norm_num)
        have h3 : Real.log (1/Real.log 2) ≤ (2:ℝ)/5 := log_one_div_log_two_le
        have hsum : Real.log (7:ℝ) + Real.log (1/Real.log 2) ≤ 2 + 2/5 := add_le_add h5 h3
        rw [gA_one_eq, log_div_log_two 7 (by norm_num)]
        linarith [hsum]
      have hp4 : (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * ((2:ℝ)^(7-1) - (2:ℝ)^(7/2)) ≤ 24.64 := by
        have h4 : (2:ℝ)^(7-1) - (2:ℝ)^(7/2) = 56 := by norm_num
        rw [h4]
        have := mul_le_mul_of_nonneg_right CB_le (by norm_num : (0:ℝ) ≤ 56)
        linarith [this]
      have ht : (35.428:ℝ) ≤ 0.5 * Real.exp 7 / 7 := by
        have h1 : (495.992:ℝ) ≤ (2.7182818283:ℝ)^7 := by norm_num
        have h2 := exp_nat_ge 7
        linarith [h1, h2]
      linarith [hb, hp1, hneg, hp3, hp4, ht]
  · -- 8 ≤ n
    have hn8' : 8 ≤ n := by omega
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnnonneg : (0:ℝ) ≤ (n:ℝ) := le_of_lt hnpos
    have hKpos : (0:ℝ) < ((n/2 : ℕ):ℝ) := by
      have : 0 < n/2 := by omega
      exact_mod_cast this
    have hK4 : 4 ≤ n/2 := by omega
    have hSH := SH_bound (n/2) (by omega)
    have hSHnn : (0:ℝ) ≤ ∑ k ∈ Finset.range (n/2), (2:ℝ)^k/((k:ℝ)+1) := by
      apply Finset.sum_nonneg
      intro k _
      positivity
    have hA1 : ((n:ℝ)/(Real.log 2 * Real.exp 1)) * (∑ k ∈ Finset.range (n/2), (2:ℝ)^k/((k:ℝ)+1))
        ≤ 1.593 * (2:ℝ)^(n/2) := by
      have hcoef : (n:ℝ)/(Real.log 2 * Real.exp 1) ≤ 0.5309 * (n:ℝ) := by
        rw [div_eq_mul_one_div]
        calc (n:ℝ) * (1/(Real.log 2 * Real.exp 1)) ≤ (n:ℝ) * 0.5309 :=
              mul_le_mul_of_nonneg_left inv_log_two_mul_exp_one_le hnnonneg
          _ = 0.5309 * (n:ℝ) := by ring
      have hnK : (n:ℝ) ≤ 2.25 * ((n/2 : ℕ):ℝ) := by
        have h1 : (n:ℝ) ≤ 2*((n/2 : ℕ):ℝ) + 1 := by
          exact_mod_cast (by omega : n ≤ 2*(n/2) + 1)
        have h2 : (4:ℝ) ≤ ((n/2 : ℕ):ℝ) := by exact_mod_cast hK4
        linarith
      calc ((n:ℝ)/(Real.log 2 * Real.exp 1)) * (∑ k ∈ Finset.range (n/2), (2:ℝ)^k/((k:ℝ)+1))
          ≤ (0.5309 * (n:ℝ)) * ((2/3) * (2:ℝ)^(n/2+1) / ((n/2 : ℕ):ℝ)) :=
            mul_le_mul hcoef hSH hSHnn (by positivity)
        _ ≤ 1.593 * (2:ℝ)^(n/2) := by
            have e1 : (0.5309 * (n:ℝ)) * ((2/3) * (2:ℝ)^(n/2+1) / ((n/2 : ℕ):ℝ))
                = (0.5309 * (4/3)) * ((n:ℝ)/((n/2 : ℕ):ℝ)) * (2:ℝ)^(n/2) := by
              rw [pow_succ]; field_simp; ring
            rw [e1]
            have h1 : (n:ℝ)/((n/2 : ℕ):ℝ) ≤ 2.25 := by
              rw [div_le_iff₀ hKpos]; linarith [hnK]
            have hp : (0:ℝ) ≤ (2:ℝ)^(n/2) := by positivity
            have h2 : ((0.5309:ℝ) * (4/3)) * ((n:ℝ)/((n/2 : ℕ):ℝ)) ≤ ((0.5309:ℝ) * (4/3)) * 2.25 :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
            have h3 : ((0.5309:ℝ) * (4/3)) * 2.25 ≤ 1.593 := by norm_num
            calc (0.5309 * (4/3)) * ((n:ℝ)/((n/2 : ℕ):ℝ)) * (2:ℝ)^(n/2)
                ≤ (0.5309 * (4/3)) * 2.25 * (2:ℝ)^(n/2) := by
                  have hh : ((0.5309:ℝ) * (4/3)) * ((n:ℝ)/((n/2 : ℕ):ℝ)) * (2:ℝ)^(n/2)
              ≤ ((0.5309:ℝ) * (4/3)) * 2.25 * (2:ℝ)^(n/2) := mul_le_mul_of_nonneg_right h2 hp
                  linarith [hh]
              _ ≤ 1.593 * (2:ℝ)^(n/2) := by
                  have hh : ((0.5309:ℝ) * (4/3)) * 2.25 * (2:ℝ)^(n/2) ≤ (1.593:ℝ) * (2:ℝ)^(n/2) :=
                mul_le_mul_of_nonneg_right h3 hp
                  linarith [hh]
    have hB1 : (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * ((2:ℝ)^(n-1) - (2:ℝ)^(n/2))
        ≤ 0.22 * (2:ℝ)^n := by
      have hXnn : (0:ℝ) ≤ (2:ℝ)^(n-1) - (2:ℝ)^(n/2) := by
        have h1 : (2:ℝ)^(n/2) ≤ (2:ℝ)^(n-1) :=
          pow_le_pow_right₀ (by norm_num) (by omega : n/2 ≤ n-1)
        linarith
      calc (Real.log (2/Real.log 2) - 1 + Real.log 2/2) * ((2:ℝ)^(n-1) - (2:ℝ)^(n/2))
          ≤ 0.44 * ((2:ℝ)^(n-1) - (2:ℝ)^(n/2)) := mul_le_mul_of_nonneg_right CB_le hXnn
        _ ≤ 0.44 * (2:ℝ)^(n-1) := by
            have h1 : (2:ℝ)^(n-1) - (2:ℝ)^(n/2) ≤ (2:ℝ)^(n-1) := by
              have : (0:ℝ) ≤ (2:ℝ)^(n/2) := by positivity
              linarith
            exact mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 0.22 * (2:ℝ)^n := by
            have h2n : (2:ℝ)^n = (2:ℝ)^(n-1) * 2 := by
              conv_lhs => rw [show n = (n-1)+1 by omega]
              exact pow_succ (2:ℝ) (n-1)
            rw [h2n]; ring
    have hg1 : gA n 1 ≤ 0.3679 * (n:ℝ) := by
      rw [gA_one_eq, log_div_log_two n (by omega)]
      have h2 := log_le_div_exp (n:ℝ) hnpos
      have h3 : Real.log (1/Real.log 2) ≤ 2/5 := log_one_div_log_two_le
      have h4 : ((n:ℝ)/Real.exp 1) ≤ 0.3679 * (n:ℝ) := by
        have h5 : (1:ℝ)/Real.exp 1 ≤ 0.3679 := by
          have ha : (1:ℝ)/Real.exp 1 ≤ 1/2.7182818283 := by
            rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
            linarith [Real.exp_one_gt_d9]
          have hb' : (1:ℝ)/2.7182818283 ≤ 0.3679 := by norm_num
          linarith [ha, hb']
        rw [div_eq_mul_one_div]
        calc (n:ℝ) * (1/Real.exp 1) ≤ (n:ℝ) * 0.3679 :=
              mul_le_mul_of_nonneg_left h5 hnnonneg
          _ = 0.3679 * (n:ℝ) := by ring
      linarith [h2, h3, h4]
    have hb : SBtau (n:ℝ) ≤ 1.593*(2:ℝ)^(n/2) + 0.3679*(n:ℝ) + 0.22*(2:ℝ)^n := by
      have hneg : -(1/2)*((2:ℝ)^(n/2) - 1) ≤ 0 := by
        have h1 : (1:ℝ) ≤ (2:ℝ)^(n/2) := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
        linarith
      linarith [hmain, hA1, hneg, hg1, hB1]
    have hpK : (2:ℝ)^(n/2) * 16 ≤ (2:ℝ)^n := by
      have h1 : n/2 ≤ n - 4 := by omega
      have h2 : (2:ℝ)^(n/2) ≤ (2:ℝ)^(n-4) := pow_le_pow_right₀ (by norm_num) h1
      have h3 : (2:ℝ)^n = (2:ℝ)^(n-4) * 16 := by
        rw [show n = (n-4)+4 by omega, pow_add]; norm_num
      rw [h3]; linarith
    have hp256 : (256:ℝ) ≤ (2:ℝ)^n := by
      have h1 : (8:ℕ) ≤ n := hn8'
      have h2 : (2:ℝ)^8 ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) h1
      norm_num at h2
      exact h2
    have hp2n : (0:ℝ) ≤ (2:ℝ)^n := by positivity
    have hbig : 1.593*(n:ℝ)*(2:ℝ)^(n/2) + 0.3679*(n:ℝ)^2 + 0.22*(n:ℝ)*(2:ℝ)^n
        ≤ 0.5*Real.exp n := by
      have hkey1 : 1.593*(n:ℝ)*(2:ℝ)^(n/2) ≤ 0.0996*(n:ℝ)*(2:ℝ)^n := by
        have h1 : (2:ℝ)^(n/2) ≤ (2:ℝ)^n/16 := by linarith [hpK]
        have e1 : 1.593*(n:ℝ)*((2:ℝ)^n/16) = ((1.593:ℝ)/16) * ((n:ℝ)*(2:ℝ)^n) := by ring
        have e2 : 0.0996*(n:ℝ)*(2:ℝ)^n = 0.0996 * ((n:ℝ)*(2:ℝ)^n) := by ring
        have h16 : ((1.593:ℝ)/16) ≤ 0.0996 := by norm_num
        have hnp : (0:ℝ) ≤ (n:ℝ)*(2:ℝ)^n := by positivity
        calc 1.593*(n:ℝ)*(2:ℝ)^(n/2) ≤ 1.593*(n:ℝ)*((2:ℝ)^n/16) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = ((1.593:ℝ)/16) * ((n:ℝ)*(2:ℝ)^n) := e1
          _ ≤ 0.0996 * ((n:ℝ)*(2:ℝ)^n) := mul_le_mul_of_nonneg_right h16 hnp
          _ = 0.0996*(n:ℝ)*(2:ℝ)^n := e2.symm
      have hkey2 : 0.3679*(n:ℝ)^2 ≤ 0.0015*(n:ℝ)^2*(2:ℝ)^n := by
        have hnum : (0.3679:ℝ) ≤ 0.0015 * (2:ℝ)^n := by
          have h1 : 0.0015 * 256 ≤ 0.0015 * (2:ℝ)^n :=
            mul_le_mul_of_nonneg_left hp256 (by norm_num)
          linarith [h1]
        have hn2 : (0:ℝ) ≤ (n:ℝ)^2 := by positivity
        calc 0.3679*(n:ℝ)^2 ≤ (0.0015 * (2:ℝ)^n)*(n:ℝ)^2 :=
              mul_le_mul_of_nonneg_right hnum hn2
          _ = 0.0015*(n:ℝ)^2*(2:ℝ)^n := by ring
      have hkey3 : (0.0996*(n:ℝ) + 0.0015*(n:ℝ)^2 + 0.22*(n:ℝ)) * (2:ℝ)^n
          ≤ 0.5*Real.exp n := by
        have hq := pow_1359_quad n hn8'
        have he := exp_nat_ge_two_mul n
        have hp : (0:ℝ) ≤ (2:ℝ)^n := hp2n
        have h4 : 0.0996*(n:ℝ) + 0.0015*(n:ℝ)^2 + 0.22*(n:ℝ)
            ≤ 0.32*(n:ℝ) + 0.0015*(n:ℝ)^2 := by linarith
        have h5 : (0.32*(n:ℝ) + 0.0015*(n:ℝ)^2) * (2:ℝ)^n
            ≤ (0.5*(1.359:ℝ)^n) * (2:ℝ)^n := mul_le_mul_of_nonneg_right hq hp
        have h6 : (0.5*(1.359:ℝ)^n) * (2:ℝ)^n = 0.5*((2:ℝ)^n*(1.359:ℝ)^n) := by ring
        have h7 : 0.5*((2:ℝ)^n*(1.359:ℝ)^n) ≤ 0.5*Real.exp n :=
          mul_le_mul_of_nonneg_left he (by norm_num)
        calc (0.0996*(n:ℝ) + 0.0015*(n:ℝ)^2 + 0.22*(n:ℝ)) * (2:ℝ)^n
            ≤ (0.32*(n:ℝ) + 0.0015*(n:ℝ)^2) * (2:ℝ)^n := mul_le_mul_of_nonneg_right h4 hp
          _ ≤ (0.5*(1.359:ℝ)^n) * (2:ℝ)^n := h5
          _ = 0.5*((2:ℝ)^n*(1.359:ℝ)^n) := h6
          _ ≤ 0.5*Real.exp n := h7
      have h8 : (0.0996*(n:ℝ) + 0.0015*(n:ℝ)^2 + 0.22*(n:ℝ)) * (2:ℝ)^n
          = 0.0996*(n:ℝ)*(2:ℝ)^n + 0.0015*(n:ℝ)^2*(2:ℝ)^n + 0.22*(n:ℝ)*(2:ℝ)^n := by ring
      rw [h8] at hkey3
      linarith [hkey1, hkey2, hkey3]
    have hb2 : (n:ℝ) * SBtau (n:ℝ) ≤ 0.5 * Real.exp n := by
      have h1 := mul_le_mul_of_nonneg_left hb hnnonneg
      nlinarith [h1, hbig]
    rw [le_div_iff₀ hnpos]
    nlinarith [hb2]

end Work.FIArea3.JointCount
