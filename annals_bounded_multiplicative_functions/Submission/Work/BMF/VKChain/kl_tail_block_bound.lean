import Mathlib
import Submission.Work.BMF.abel_ioc_bound
import Submission.Work.BMF.norm_cpow_I_sub_one_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Work.BMF.VKChain

open Finset

/-! ## Elementary estimates for exponentials of purely imaginary arguments -/

/-- `2λ/π ≤ 2 sin (x/2)` for `0 < λ ≤ x ≤ 2λ ≤ π`. -/
private lemma two_mul_lam_div_pi_le_two_sin {lam x : ℝ} (hlam : 0 < lam)
    (hlam2 : 2 * lam ≤ Real.pi) (hlo : lam ≤ x) (hhi : x ≤ 2 * lam) :
    2 * lam / Real.pi ≤ 2 * Real.sin (x / 2) := by
  have hx0 : 0 ≤ x / 2 := by linarith
  have hxpi : x / 2 ≤ Real.pi / 2 := by linarith
  have h := Real.mul_le_sin hx0 hxpi
  have h2 : (2 : ℝ) / Real.pi * (x / 2) = x / Real.pi := by ring
  rw [h2] at h
  have h3 : lam / Real.pi ≤ x / Real.pi := div_le_div_of_nonneg_right hlo Real.pi_pos.le
  have h4 : 2 * lam / Real.pi = 2 * (lam / Real.pi) := by ring
  rw [h4]
  linarith

/-- `2λ/π ≤ ‖exp (-I x) - 1‖` for `0 < λ ≤ x ≤ 2λ ≤ π`. -/
private lemma two_mul_lam_div_pi_le_norm_exp_neg_I_sub_one {lam x : ℝ} (hlam : 0 < lam)
    (hlam2 : 2 * lam ≤ Real.pi) (hlo : lam ≤ x) (hhi : x ≤ 2 * lam) :
    2 * lam / Real.pi ≤ ‖Complex.exp (Complex.I * ((-x : ℝ) : ℂ)) - 1‖ := by
  have hsin : 0 ≤ 2 * Real.sin (x / 2) :=
    mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show (-x) / 2 = -(x / 2) by ring, Real.sin_neg, mul_neg, abs_neg, abs_of_nonneg hsin]
  exact two_mul_lam_div_pi_le_two_sin hlam hlam2 hlo hhi

/-- `‖exp (-I b) - exp (-I a)‖ ≤ |a - b|`. -/
private lemma norm_exp_neg_I_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * ((-b : ℝ) : ℂ)) - Complex.exp (Complex.I * ((-a : ℝ) : ℂ))‖ ≤
      |a - b| := by
  have harg : Complex.I * ((-a : ℝ) : ℂ) + Complex.I * (((a - b : ℝ)) : ℂ)
      = Complex.I * ((-b : ℝ) : ℂ) := by push_cast; ring
  have hdecomp : Complex.exp (Complex.I * ((-b : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((-a : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((-a : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * (((a - b : ℝ)) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, harg]
  rw [hdecomp, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  exact Work.BMF.abs_two_mul_sin_half_le (a - b)

/-- `‖A⁻¹ - B⁻¹‖ ≤ e / m²` when `m ≤ ‖A‖`, `m ≤ ‖B‖` and `‖B - A‖ ≤ e`. -/
private lemma norm_inv_sub_inv_le {A B : ℂ} {m e : ℝ} (hm : 0 < m) (he : 0 ≤ e)
    (hA : m ≤ ‖A‖) (hB : m ≤ ‖B‖) (heAB : ‖B - A‖ ≤ e) :
    ‖A⁻¹ - B⁻¹‖ ≤ e / m ^ 2 := by
  have hA0 : A ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hm hA))
  have hB0 : B ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hm hB))
  have hid : A⁻¹ - B⁻¹ = (B - A) * ((A * B))⁻¹ := by
    field_simp
  rw [hid, norm_mul, norm_inv, norm_mul]
  have hpos : 0 < m * m := mul_pos hm hm
  have hAB : m * m ≤ ‖A‖ * ‖B‖ := mul_le_mul hA hB hm.le (norm_nonneg A)
  have hinv : (‖A‖ * ‖B‖)⁻¹ ≤ (m * m)⁻¹ :=
    (inv_le_inv₀ (mul_pos (lt_of_lt_of_le hm hA) (lt_of_lt_of_le hm hB)) hpos).mpr hAB
  calc ‖B - A‖ * (‖A‖ * ‖B‖)⁻¹ ≤ e * (m * m)⁻¹ :=
        mul_le_mul heAB hinv (inv_nonneg.mpr (mul_nonneg (norm_nonneg A) (norm_nonneg B))) he
    _ = e / m ^ 2 := by ring

/-- Telescoping: `∑_{K < j ≤ m} (z (j+1) - z j) = z (m+1) - z (K+1)`. -/
private lemma tel_sum (z : ℕ → ℂ) {K m : ℕ} (h : K ≤ m) :
    ∑ j ∈ Finset.Ioc K m, (z (j + 1) - z j) = z (m + 1) - z (K + 1) := by
  have hIoc : Finset.Ioc K m = Finset.Icc (K + 1) m := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc]
  have key : ∑ j ∈ Finset.Icc (K + 1) m, (z (j + 1) - z j)
      = -∑ j ∈ Finset.Icc (K + 1) m, (z j - z (j + 1)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [key, Work.BMF.sum_Icc_sub_telescope z (K + 1) m (by omega)]
  ring

/-- **Abstract Kuzmin-type block bound.**  If `z` is a sequence of unit complex numbers whose
consecutive ratios are `w n`, if `‖w n - 1‖ ≥ 2λ/π` and `‖w (n+1) - w n‖ ≤ g n` with
`∑ g n ≤ λ`, then any block of consecutive terms starting at `K` is bounded by
`1 + π/λ + π²/(2λ)`. -/
private theorem exp_sum_abstract (z w : ℕ → ℂ) (g : ℕ → ℝ) (K k : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hlam2 : 2 * lam ≤ Real.pi)
    (hg0 : ∀ n ∈ Finset.Ioc K (k - 2), 0 ≤ g n)
    (hsumg : ∑ n ∈ Finset.Ioc K (k - 2), g n ≤ lam)
    (hz1 : ∀ n, ‖z n‖ = 1)
    (hz : ∀ n ∈ Finset.Ioc K (k - 1), z (n + 1) = z n * w n)
    (hwlo : ∀ n ∈ Finset.Ioc K (k - 1), 2 * lam / Real.pi ≤ ‖w n - 1‖)
    (hwdiff : ∀ n ∈ Finset.Ioc K (k - 2), ‖w (n + 1) - w n‖ ≤ g n) :
    ‖∑ j ∈ Finset.Ioc K k, z j‖ ≤ 1 + Real.pi / lam + Real.pi ^ 2 / (2 * lam) := by
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hm0 : 0 < 2 * lam / Real.pi := div_pos (by linarith) hpi0
  by_cases hk : k ≤ K + 1
  · by_cases hk0 : k ≤ K
    · have hempty : Finset.Ioc K k = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, norm_zero]
      have h1 : 0 ≤ Real.pi / lam := div_nonneg hpi0.le hlam.le
      have h2 : 0 ≤ Real.pi ^ 2 / (2 * lam) := div_nonneg (sq_nonneg _) (by linarith)
      linarith
    · have hk' : k = K + 1 := by omega
      subst hk'
      have hs : ∑ j ∈ Finset.Ioc K (K + 1), z j = z (K + 1) := by
        rw [Finset.sum_Ioc_succ_top (le_refl K) z, Finset.Ioc_self, Finset.sum_empty, zero_add]
      rw [hs, hz1]
      have h1 : 0 ≤ Real.pi / lam := div_nonneg hpi0.le hlam.le
      have h2 : 0 ≤ Real.pi ^ 2 / (2 * lam) := div_nonneg (sq_nonneg _) (by linarith)
      linarith
  · push_neg at hk
    have hkN : K < k - 1 := by omega
    have hw1pos : ∀ n ∈ Finset.Ioc K (k - 1), 0 < ‖w n - 1‖ :=
      fun n hn => lt_of_lt_of_le hm0 (hwlo n hn)
    have hwne : ∀ n ∈ Finset.Ioc K (k - 1), w n - 1 ≠ 0 :=
      fun n hn => norm_ne_zero_iff.mp (ne_of_gt (hw1pos n hn))
    set c : ℕ → ℂ := fun n => (w n - 1)⁻¹ with hc
    have hzn : ∀ n ∈ Finset.Ioc K (k - 1), z n = c n * (z (n + 1) - z n) := by
      intro n hn
      have h1 : z (n + 1) - z n = z n * (w n - 1) := by rw [hz n hn]; ring
      have h2 := hwne n hn
      rw [h1, hc]
      simp only
      rw [mul_comm (z n) (w n - 1), ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    set D : ℕ → ℂ := fun j => z (j + 1) - z j with hD
    set A : ℕ → ℂ := fun m => ∑ j ∈ Finset.Ioc K m, D j with hA
    have hA0 : A K = 0 := by rw [hA]; simp
    have hstep : ∀ m, K ≤ m → A (m + 1) = A m + D (m + 1) := by
      intro m hm
      rw [hA]; simp only
      rw [Finset.sum_Ioc_succ_top hm D]
    have hid := ioc_abel_identity D c A K (k - 1) hA0 hstep hkN
    have hsub : (k - 1) - 1 = k - 2 := by omega
    rw [hsub] at hid
    have hAb : ∀ m, K ≤ m → ‖A m‖ ≤ 2 := by
      intro m hm
      have h1 : A m = z (m + 1) - z (K + 1) := by
        rw [hA]; simp only
        rw [hD]; simp only
        exact tel_sum z hm
      rw [h1]
      calc ‖z (m + 1) - z (K + 1)‖ ≤ ‖z (m + 1)‖ + ‖z (K + 1)‖ := norm_sub_le _ _
        _ = 2 := by rw [hz1, hz1]; norm_num
    have hc1 : ‖c (k - 1)‖ ≤ Real.pi / (2 * lam) := by
      have hmem : k - 1 ∈ Finset.Ioc K (k - 1) := Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩
      have hX : 0 < ‖w (k - 1) - 1‖ := hw1pos _ hmem
      rw [hc]; simp only
      rw [norm_inv]
      calc (‖w (k - 1) - 1‖)⁻¹ ≤ (2 * lam / Real.pi)⁻¹ :=
            (inv_le_inv₀ hX hm0).mpr (hwlo _ hmem)
        _ = Real.pi / (2 * lam) := by rw [inv_div]
    have hcdiff : ∀ n ∈ Finset.Ioc K (k - 2),
        ‖c n - c (n + 1)‖ ≤ g n * (Real.pi ^ 2 / (4 * lam ^ 2)) := by
      intro n hn
      have hn1 : n ∈ Finset.Ioc K (k - 1) := by
        rw [Finset.mem_Ioc] at hn ⊢; exact ⟨hn.1, by omega⟩
      have hn1' : n + 1 ∈ Finset.Ioc K (k - 1) := by
        rw [Finset.mem_Ioc] at hn ⊢; exact ⟨by omega, by omega⟩
      have hlow : 2 * lam / Real.pi ≤ ‖w n - 1‖ := hwlo n hn1
      have hlow' : 2 * lam / Real.pi ≤ ‖w (n + 1) - 1‖ := hwlo (n + 1) hn1'
      have hg := hwdiff n hn
      have he0 := hg0 n hn
      have hg' : ‖(w (n + 1) - 1) - (w n - 1)‖ ≤ g n := by
        have heq2 : (w (n + 1) - 1) - (w n - 1) = w (n + 1) - w n := by ring
        rw [heq2]; exact hg
      have hmain : ‖(w n - 1)⁻¹ - (w (n + 1) - 1)⁻¹‖ ≤ g n / (2 * lam / Real.pi) ^ 2 :=
        norm_inv_sub_inv_le hm0 he0 hlow hlow' hg'
      have heq : g n / (2 * lam / Real.pi) ^ 2 = g n * (Real.pi ^ 2 / (4 * lam ^ 2)) := by
        field_simp
        try ring
      calc ‖c n - c (n + 1)‖ = ‖(w n - 1)⁻¹ - (w (n + 1) - 1)⁻¹‖ := by rw [hc]
        _ ≤ g n / (2 * lam / Real.pi) ^ 2 := hmain
        _ = g n * (Real.pi ^ 2 / (4 * lam ^ 2)) := heq
    have hsplit : ∑ j ∈ Finset.Ioc K k, z j = (∑ j ∈ Finset.Ioc K (k - 1), z j) + z k := by
      have h := Finset.sum_Ioc_succ_top (show K ≤ k - 1 by omega) z
      rwa [show (k - 1) + 1 = k by omega] at h
    have hzsum : ∑ j ∈ Finset.Ioc K (k - 1), z j
        = ∑ j ∈ Finset.Ioc K (k - 1), c j * D j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hzn j hj, hD]
    have hnorm : ‖∑ j ∈ Finset.Ioc K (k - 1), z j‖
        ≤ 2 * ‖c (k - 1)‖ + 2 * ∑ n ∈ Finset.Ioc K (k - 2), ‖c n - c (n + 1)‖ := by
      rw [hzsum, hid]
      have h1 : ‖c (k - 1) * A (k - 1)‖ ≤ 2 * ‖c (k - 1)‖ := by
        rw [norm_mul]
        calc ‖c (k - 1)‖ * ‖A (k - 1)‖ ≤ ‖c (k - 1)‖ * 2 :=
              mul_le_mul_of_nonneg_left (hAb (k - 1) (by omega)) (norm_nonneg _)
          _ = 2 * ‖c (k - 1)‖ := by ring
      have h2 : ‖∑ n ∈ Finset.Ioc K (k - 2), (c n - c (n + 1)) * A n‖
          ≤ 2 * ∑ n ∈ Finset.Ioc K (k - 2), ‖c n - c (n + 1)‖ := by
        calc ‖∑ n ∈ Finset.Ioc K (k - 2), (c n - c (n + 1)) * A n‖
            ≤ ∑ n ∈ Finset.Ioc K (k - 2), ‖(c n - c (n + 1)) * A n‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Ioc K (k - 2), ‖c n - c (n + 1)‖ * 2 :=
              Finset.sum_le_sum (fun n hn => by
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left
                  (hAb n (by have h := (Finset.mem_Ioc.mp hn).1; omega)) (norm_nonneg _))
          _ = 2 * ∑ n ∈ Finset.Ioc K (k - 2), ‖c n - c (n + 1)‖ := by
              rw [← Finset.sum_mul, mul_comm]
      calc ‖c (k - 1) * A (k - 1) + ∑ n ∈ Finset.Ioc K (k - 2), (c n - c (n + 1)) * A n‖
          ≤ ‖c (k - 1) * A (k - 1)‖ +
              ‖∑ n ∈ Finset.Ioc K (k - 2), (c n - c (n + 1)) * A n‖ := norm_add_le _ _
        _ ≤ 2 * ‖c (k - 1)‖ + 2 * ∑ n ∈ Finset.Ioc K (k - 2), ‖c n - c (n + 1)‖ :=
              add_le_add h1 h2
    have hsum_cd : ∑ n ∈ Finset.Ioc K (k - 2), ‖c n - c (n + 1)‖
        ≤ lam * (Real.pi ^ 2 / (4 * lam ^ 2)) := by
      refine le_trans (Finset.sum_le_sum hcdiff) ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hsumg (by positivity)
    rw [hsplit]
    calc ‖(∑ j ∈ Finset.Ioc K (k - 1), z j) + z k‖
        ≤ ‖∑ j ∈ Finset.Ioc K (k - 1), z j‖ + ‖z k‖ := norm_add_le _ _
      _ ≤ (2 * ‖c (k - 1)‖ + 2 * ∑ n ∈ Finset.Ioc K (k - 2), ‖c n - c (n + 1)‖) + 1 := by
            rw [hz1]; linarith
      _ ≤ (2 * (Real.pi / (2 * lam)) + 2 * (lam * (Real.pi ^ 2 / (4 * lam ^ 2)))) + 1 := by
            linarith
      _ = 1 + Real.pi / lam + Real.pi ^ 2 / (2 * lam) := by field_simp; ring

/-- Splitting off the real part of the exponent. -/
private lemma cpow_split (u σ t : ℝ) (hu : 0 < u) (n : ℕ) :
    ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) =
      ((((n : ℝ) + u) ^ (-σ) : ℝ) : ℂ) *
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
  have hx : (0 : ℝ) < (n : ℝ) + u := by positivity
  have hne : ((((n : ℝ) + u : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  rw [show -((σ : ℂ) + (t : ℂ) * Complex.I) = -(σ : ℂ) + (-(Complex.I * (t : ℂ))) by ring]
  rw [Complex.cpow_add _ _ hne, Complex.ofReal_cpow hx.le]
  simp only [Complex.ofReal_neg]

/-- `(x : ℂ) ^ (-(I t)) = exp (I (-(t log x)))` for `x > 0`. -/
private lemma cpow_eq_exp (u t : ℝ) (hu : 0 < u) (n : ℕ) :
    ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) =
      Complex.exp (Complex.I * ((-(t * Real.log ((n : ℝ) + u)) : ℝ) : ℂ)) := by
  have hx : (0 : ℝ) < (n : ℝ) + u := by positivity
  have hne : ((((n : ℝ) + u : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

/-- **Block bound for the unweighted exponential sum.**  For `3 ≤ K`, `K < k ≤ 2K` and `t ≤ K`,
`‖∑_{K < j ≤ k} (j+u)^{-it}‖ ≤ 30 K / t`. -/
private theorem exp_sum_block {u t : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    {K k : ℕ} (hK : 3 ≤ K) (hKk : K < k) (hkR : (k : ℝ) ≤ 2 * K) (htK : t ≤ (K : ℝ)) :
    ‖∑ j ∈ Finset.Ioc K k, ((((j : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
      30 * (K : ℝ) / t := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  by_cases hkc : k ≤ K + 1
  · have hk' : k = K + 1 := by omega
    subst hk'
    rw [Finset.sum_Ioc_succ_top (le_refl K), Finset.Ioc_self, Finset.sum_empty, zero_add,
      cpow_eq_exp u t hu (K + 1), Complex.norm_exp_I_mul_ofReal]
    rw [le_div_iff₀ ht]
    nlinarith [htK, hK3, hKR]
  · push_neg at hkc
    have hden : (0 : ℝ) < 2 * (K : ℝ) + u := by linarith
    set lam : ℝ := t / (2 * (K : ℝ) + u) with hlam
    have hlampos : 0 < lam := by rw [hlam]; positivity
    have hlam2 : 2 * lam ≤ Real.pi := by
      have hle : lam ≤ 1 / 2 := by
        rw [hlam, div_le_iff₀ hden]
        linarith [htK]
      linarith [Real.pi_gt_three]
    set del : ℕ → ℝ := fun n => t * Real.log ((((n : ℝ) + 1 + u) / ((n : ℝ) + u))) with hdel
    set z : ℕ → ℂ := fun n => Complex.exp (Complex.I * ((-(t * Real.log ((n : ℝ) + u)) : ℝ) : ℂ))
      with hzdef
    set w : ℕ → ℂ := fun n => Complex.exp (Complex.I * ((-(del n) : ℝ) : ℂ)) with hw
    set g : ℕ → ℝ := fun n => del n - del (n + 1) with hg
    have hdel_lo : ∀ n ∈ Finset.Ioc K (k - 1), lam ≤ del n := by
      intro n hn
      have hnle : n ≤ k - 1 := (Finset.mem_Ioc.mp hn).2
      have hx : 0 < ((n : ℝ) + 1 + u) / ((n : ℝ) + u) := by positivity
      have hlog : (1 : ℝ) / ((n : ℝ) + 1 + u)
          ≤ Real.log (((n : ℝ) + 1 + u) / ((n : ℝ) + u)) := by
        have h1 := Real.one_sub_inv_le_log_of_pos hx
        have h2 : 1 - (((n : ℝ) + 1 + u) / ((n : ℝ) + u))⁻¹ = 1 / ((n : ℝ) + 1 + u) := by
          rw [inv_div]
          field_simp
          ring
        rwa [h2] at h1
      have hn1 : (n : ℝ) + 1 ≤ 2 * (K : ℝ) := by
        have hk1 : 1 ≤ k := by omega
        have h1 : (n : ℝ) ≤ (k : ℝ) - 1 := by
          calc (n : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hnle
            _ = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1]; norm_num
        linarith [hkR]
      have h3 : (1 : ℝ) / (2 * (K : ℝ) + u) ≤ 1 / ((n : ℝ) + 1 + u) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h4 : (1 : ℝ) / (2 * (K : ℝ) + u)
          ≤ Real.log (((n : ℝ) + 1 + u) / ((n : ℝ) + u)) := le_trans h3 hlog
      rw [hlam]
      calc t / (2 * (K : ℝ) + u) = t * (1 / (2 * (K : ℝ) + u)) := by ring
        _ ≤ t * Real.log (((n : ℝ) + 1 + u) / ((n : ℝ) + u)) :=
            mul_le_mul_of_nonneg_left h4 ht.le
        _ = del n := by rw [hdel]
    have hdel_hi : ∀ n ∈ Finset.Ioc K (k - 1), del n ≤ 2 * lam := by
      intro n hn
      have hnK : K < n := (Finset.mem_Ioc.mp hn).1
      have hx : 0 < ((n : ℝ) + 1 + u) / ((n : ℝ) + u) := by positivity
      have hlog : Real.log (((n : ℝ) + 1 + u) / ((n : ℝ) + u)) ≤ 1 / ((n : ℝ) + u) := by
        have h1 := Real.log_le_sub_one_of_pos hx
        have h2 : ((n : ℝ) + 1 + u) / ((n : ℝ) + u) - 1 = 1 / ((n : ℝ) + u) := by
          field_simp
          ring
        rwa [h2] at h1
      have hnK' : (K : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : K + 1 ≤ n)
      have h3 : (1 : ℝ) / ((n : ℝ) + u) ≤ 1 / ((K : ℝ) + u) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h4 : (1 : ℝ) / ((K : ℝ) + u) ≤ 2 / (2 * (K : ℝ) + u) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (K : ℝ) + u), div_mul_eq_mul_div,
          div_le_iff₀ (by linarith : (0 : ℝ) < (K : ℝ) + u)]
        linarith
      have h5 : Real.log (((n : ℝ) + 1 + u) / ((n : ℝ) + u))
          ≤ 2 / (2 * (K : ℝ) + u) := le_trans hlog (le_trans h3 h4)
      rw [hlam]
      calc del n = t * Real.log (((n : ℝ) + 1 + u) / ((n : ℝ) + u)) := by rw [hdel]
        _ ≤ t * (2 / (2 * (K : ℝ) + u)) := mul_le_mul_of_nonneg_left h5 ht.le
        _ = 2 * (t / (2 * (K : ℝ) + u)) := by ring
    have hdel_dec : ∀ n, del (n + 1) ≤ del n := by
      intro n
      have hstep1 : ((((n + 1 : ℕ) : ℝ) + 1 + u) / (((n + 1 : ℕ) : ℝ) + u))
          = ((n : ℝ) + 2 + u) / ((n : ℝ) + 1 + u) := by push_cast; ring
      have h1 : 0 < ((n : ℝ) + 2 + u) / ((n : ℝ) + 1 + u) := by positivity
      have h2 : 0 < ((n : ℝ) + 1 + u) / ((n : ℝ) + u) := by positivity
      have h3 : ((n : ℝ) + 2 + u) / ((n : ℝ) + 1 + u) ≤
          ((n : ℝ) + 1 + u) / ((n : ℝ) + u) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + u), div_mul_eq_mul_div,
          div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1 + u)]
        nlinarith
      have h4 := Real.log_le_log h1 h3
      calc del (n + 1) = t * Real.log ((((n + 1 : ℕ) : ℝ) + 1 + u) / (((n + 1 : ℕ) : ℝ) + u)) :=
            by rw [hdel]
        _ = t * Real.log (((n : ℝ) + 2 + u) / ((n : ℝ) + 1 + u)) := by rw [hstep1]
        _ ≤ t * Real.log (((n : ℝ) + 1 + u) / ((n : ℝ) + u)) :=
            mul_le_mul_of_nonneg_left h4 ht.le
        _ = del n := by rw [hdel]
    have hg0 : ∀ n ∈ Finset.Ioc K (k - 2), 0 ≤ g n := by
      intro n hn
      rw [hg]; simp only
      exact sub_nonneg.mpr (hdel_dec n)
    have hsumg : ∑ n ∈ Finset.Ioc K (k - 2), g n ≤ lam := by
      have hIcc : Finset.Ioc K (k - 2) = Finset.Icc (K + 1) (k - 2) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
      have htel : ∑ n ∈ Finset.Icc (K + 1) (k - 2), (del n - del (n + 1))
          = del (K + 1) - del (k - 1) := by
        have h := Work.BMF.sum_Icc_sub_telescope del (K + 1) (k - 2) (by omega)
        rwa [show k - 2 + 1 = k - 1 by omega] at h
      have hmem1 : (K + 1) ∈ Finset.Ioc K (k - 1) := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      have hmem2 : (k - 1) ∈ Finset.Ioc K (k - 1) := Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩
      have h1 : del (K + 1) ≤ 2 * lam := hdel_hi (K + 1) hmem1
      have h2 : lam ≤ del (k - 1) := hdel_lo (k - 1) hmem2
      calc ∑ n ∈ Finset.Ioc K (k - 2), g n
          = ∑ n ∈ Finset.Ioc K (k - 2), (del n - del (n + 1)) := by
            apply Finset.sum_congr rfl; intro n _; rw [hg]
        _ = del (K + 1) - del (k - 1) := by rw [hIcc, htel]
        _ ≤ lam := by linarith
    have hz1 : ∀ n, ‖z n‖ = 1 := by
      intro n
      rw [hzdef]; simp only
      exact Complex.norm_exp_I_mul_ofReal _
    have hzrel : ∀ n ∈ Finset.Ioc K (k - 1), z (n + 1) = z n * w n := by
      intro n hn
      have hstep1 : ((((n + 1 : ℕ) : ℝ) + u)) = (n : ℝ) + 1 + u := by push_cast; ring
      rw [hzdef, hw, hdel]
      simp only [hstep1]
      rw [← Complex.exp_add]
      congr 1
      rw [Real.log_div (by positivity) (by positivity)]
      push_cast
      ring
    have hwlo : ∀ n ∈ Finset.Ioc K (k - 1), 2 * lam / Real.pi ≤ ‖w n - 1‖ := by
      intro n hn
      rw [hw]; simp only
      rw [hlam]
      exact two_mul_lam_div_pi_le_norm_exp_neg_I_sub_one hlampos hlam2 (hdel_lo n hn)
        (hdel_hi n hn)
    have hwdiff : ∀ n ∈ Finset.Ioc K (k - 2), ‖w (n + 1) - w n‖ ≤ g n := by
      intro n hn
      have h1 : ‖w (n + 1) - w n‖ ≤ |del n - del (n + 1)| := by
        rw [hw]; simp only
        exact norm_exp_neg_I_sub_le (del n) (del (n + 1))
      have h2 : g n = del n - del (n + 1) := by rw [hg]
      have h3 : (0 : ℝ) ≤ del n - del (n + 1) := sub_nonneg.mpr (hdel_dec n)
      rw [h2]
      rw [abs_of_nonneg h3] at h1
      exact h1
    have hmain := exp_sum_abstract z w g K k hlampos hlam2 hg0 hsumg hz1 hzrel hwlo hwdiff
    have hzeq : ∑ j ∈ Finset.Ioc K k, z j
        = ∑ j ∈ Finset.Ioc K k, ((((j : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hzdef]; simp only
      exact (cpow_eq_exp u t hu j).symm
    rw [hzeq] at hmain
    refine le_trans hmain ?_
    rw [hlam, le_div_iff₀ ht]
    have e1 : Real.pi / (t / (2 * (K : ℝ) + u)) * t = Real.pi * (2 * (K : ℝ) + u) := by
      rw [div_div_eq_mul_div]
      field_simp
    have e2 : Real.pi ^ 2 / (2 * (t / (2 * (K : ℝ) + u))) * t
        = Real.pi ^ 2 * (2 * (K : ℝ) + u) / 2 := by
      rw [← mul_div_assoc, div_div_eq_mul_div]
      field_simp
      try ring
    have hexp : (1 + Real.pi / (t / (2 * (K : ℝ) + u)) +
        Real.pi ^ 2 / (2 * (t / (2 * (K : ℝ) + u)))) * t
        = t + Real.pi * (2 * (K : ℝ) + u) + Real.pi ^ 2 * (2 * (K : ℝ) + u) / 2 := by
      rw [add_mul, add_mul, one_mul, e1, e2]
    rw [hexp]
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    have h2Ku : 0 ≤ 2 * (K : ℝ) + u := by linarith
    nlinarith [hpi2, h2Ku, htK, hu1, hK3, Real.pi_lt_four, Real.pi_gt_three]

theorem kl_tail_block_bound {u σ t : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hσ : 0 < σ) (ht : 3 ≤ t)
    {K R : ℕ} (hRK : K < R) (hR2K : (R : ℝ) ≤ 2 * K) (htK : t ≤ (K : ℝ)) :
    ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      12 * Real.pi * (K : ℝ) ^ (1 - σ) / t := by
  have hK : 3 ≤ K := by
    have : (3 : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast this
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  set a : ℕ → ℂ := fun n => ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) with ha
  set wr : ℕ → ℝ := fun n => ((n : ℝ) + u) ^ (-σ) with hwr
  have hsum_eq : ∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^
        (-((σ : ℂ) + (t : ℂ) * Complex.I)) = ∑ n ∈ Finset.Ioc K R, (wr n : ℂ) * a n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ha, hwr]; simp only
    exact cpow_split u σ t hu n
  have hB : 0 ≤ 30 * (K : ℝ) / t := by positivity
  have hw0 : ∀ n ∈ Finset.Ioc K R, 0 ≤ wr n := by
    intro n hn
    rw [hwr]; simp only
    exact Real.rpow_nonneg (by positivity) _
  have hwmono : ∀ n, K ≤ n → n < R → wr (n + 1) ≤ wr n := by
    intro n hn1 hn2
    rw [hwr]; simp only
    exact Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ) + u)
      (by push_cast; linarith) (by linarith : -σ ≤ 0)
  have hpartial : ∀ k, K < k → k ≤ R → ‖∑ j ∈ Finset.Ioc K k, a j‖ ≤ 30 * (K : ℝ) / t := by
    intro k hk1 hk2
    have hkR : (k : ℝ) ≤ 2 * (K : ℝ) := le_trans (by exact_mod_cast hk2) hR2K
    rw [ha]; simp only
    exact exp_sum_block hu hu1 (by linarith : (0 : ℝ) < t) hK hk1 hkR htK
  have habel := abel_ioc_bound a wr K R (30 * (K : ℝ) / t) hRK hB hw0 hwmono hpartial
  rw [hsum_eq]
  refine le_trans habel ?_
  have hwr_le : wr (K + 1) ≤ (K : ℝ) ^ (-σ) := by
    rw [hwr]; simp only
    exact Real.rpow_le_rpow_of_nonpos hKR (by push_cast; linarith [hu]) (by linarith : -σ ≤ 0)
  have hKpow : (K : ℝ) ^ (1 - σ) = (K : ℝ) * (K : ℝ) ^ (-σ) := by
    rw [show (1 : ℝ) - σ = 1 + (-σ) by ring, Real.rpow_add hKR, Real.rpow_one]
  calc (30 * (K : ℝ) / t) * wr (K + 1)
      ≤ (30 * (K : ℝ) / t) * (K : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_left hwr_le (by positivity)
    _ = 30 * (K : ℝ) ^ (1 - σ) / t := by rw [hKpow]; ring
    _ ≤ 12 * Real.pi * (K : ℝ) ^ (1 - σ) / t := by
        rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < t)]
        exact mul_le_mul_of_nonneg_right
          (by linarith [Real.pi_gt_three] : (30 : ℝ) ≤ 12 * Real.pi)
          (Real.rpow_nonneg hKR.le _)

end Work.BMF.VKChain
