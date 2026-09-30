import Mathlib
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.sampled_mean_value_blocks
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators
open BoundedMultiplicativeFunctions

noncomputable section

/-! ## The well-spaced mean-square bound for the remainder polynomial -/

lemma exp_inv_le_four {K : ℝ} (hK : 1 ≤ K) : Real.exp (1 / K) ≤ 4 := by
  have hKpos : (0 : ℝ) < K := by linarith
  have h1 : (1 : ℝ) / K ≤ 1 := by rw [div_le_one hKpos]; linarith
  have h2 : Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
  have h3 : Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
  linarith

lemma sum_inv_sq_Icc_le (N M : ℕ) (hN : 1 ≤ N) (hM : M ≤ 16 * N) :
    (∑ n ∈ Finset.Icc N M, (1 : ℝ) / (n : ℝ) ^ 2) ≤ 16 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  by_cases hNM : N ≤ M
  · have h1 : ∀ n ∈ Finset.Icc N M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((N : ℝ) ^ 2) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hsq : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      exact one_div_le_one_div_of_le (by positivity) hsq
    have hcard : ((Finset.Icc N M).card : ℝ) ≤ ((16 * N : ℕ) : ℝ) := by
      rw [Nat.card_Icc]
      have hle : M + 1 - N ≤ 16 * N := by omega
      exact_mod_cast hle
    calc (∑ n ∈ Finset.Icc N M, (1 : ℝ) / (n : ℝ) ^ 2)
        ≤ ∑ n ∈ Finset.Icc N M, 1 / ((N : ℝ) ^ 2) := Finset.sum_le_sum h1
      _ = ((Finset.Icc N M).card : ℝ) * (1 / ((N : ℝ) ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((16 * N : ℕ) : ℝ) * (1 / ((N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 16 / (N : ℝ) := by
          rw [show ((16 * N : ℕ) : ℝ) = 16 * (N : ℝ) by push_cast; ring]
          rw [eq_div_iff hN0]
          field_simp <;> ring
  · have hempty : Finset.Icc N M = ∅ := Finset.Icc_eq_empty_iff.mpr (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

/-- Conjugation identity for `cpow` at a natural number. -/
lemma conj_cpow_nat (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ z) = (n : ℂ) ^ ((starRingEnd ℂ) z) := by
  rw [← Complex.ofReal_natCast,
    Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg (Nat.cast_nonneg n), Complex.ofReal_natCast]

/-- **Mean square of the remainder polynomial over a well-spaced set.**

For a `1`-separated family `t : Fin R → ℝ` inside `[-TT,TT]`,
`Σ_r ‖remPolyR b P Q K X₁ X₂ j (t r)‖² ≤ C (1 + TT·e^{j/K}/X₁)`, uniformly in everything (in
particular in `R`). -/
theorem remPolyREnergyLe :
    ∃ C : ℝ, 0 < C ∧
      ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (P Q K X₁ X₂ : ℝ) (j : ℕ) (TT : ℝ) (R : ℕ) (t : Fin R → ℝ),
        1 ≤ X₁ → 1 ≤ K → 0 ≤ TT → X₂ ≤ 4 * X₁ →
        1 ≤ X₁ * Real.exp (-(((j : ℝ) + 1) / K)) →
        (∀ i, t i ∈ Set.Icc (-TT) TT) →
        (∀ i i' : Fin R, i ≠ i' → 1 ≤ |t i - t i'|) →
        (∑ r, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j (t r)‖ ^ 2)
          ≤ C * (1 + TT * Real.exp ((j : ℝ) / K) / X₁) := by
  obtain ⟨Cs, hCspos, hsmv⟩ := Work.BMF.mr_direct.sampled_mean_value_blocks
  refine ⟨Cs * 17 * 512, by positivity, ?_⟩
  intro b hb P Q K X₁ X₂ j TT R t hX₁ hK hTT hX₂ hA hIcc hsep
  set A : ℝ := X₁ * Real.exp (-((j : ℝ) + 1) / K) with hAdef
  set B : ℝ := X₂ * Real.exp (-(j : ℝ) / K) with hBdef
  have hX₁pos : 0 < X₁ := by linarith
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    have h : Real.exp (-(((j : ℝ) + 1) / K)) = Real.exp (-((j : ℝ) + 1) / K) := by
      congr 1
      rw [neg_div]
    rw [← h]
    exact hA
  have hexpK : Real.exp (1 / K) ≤ 4 := exp_inv_le_four hK
  -- `B ≤ 16 A`
  have hBA : B ≤ 16 * A := by
    rw [hBdef, hAdef]
    have hsplit : Real.exp ((-(j : ℝ)) / K)
        = Real.exp ((-((j : ℝ) + 1)) / K) * Real.exp (1 / K) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit]
    have hEpos : 0 < Real.exp ((-((j : ℝ) + 1)) / K) := Real.exp_pos _
    have h3 : Real.exp ((-((j : ℝ) + 1)) / K) * Real.exp (1 / K)
        ≤ Real.exp ((-((j : ℝ) + 1)) / K) * 4 :=
      mul_le_mul_of_nonneg_left hexpK (le_of_lt hEpos)
    calc X₂ * (Real.exp ((-((j : ℝ) + 1)) / K) * Real.exp (1 / K))
        ≤ (4 * X₁) * (Real.exp ((-((j : ℝ) + 1)) / K) * Real.exp (1 / K)) :=
          mul_le_mul_of_nonneg_right hX₂ (by positivity)
      _ ≤ (4 * X₁) * (Real.exp ((-((j : ℝ) + 1)) / K) * 4) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 16 * (X₁ * Real.exp ((-((j : ℝ) + 1)) / K)) := by ring
  -- `⌊B⌋₊ ≤ 16 ⌈A⌉₊`
  have hMN : ⌊B⌋₊ ≤ ⌈A⌉₊ * 16 := by
    have hAN : A ≤ ((⌈A⌉₊ : ℕ) : ℝ) := Nat.le_ceil A
    by_cases hB1 : B < 1
    · rw [Nat.floor_eq_zero.mpr hB1]
      positivity
    · push_neg at hB1
      have hBnn : (0 : ℝ) ≤ B := by linarith
      have hb1 : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le hBnn
      have hb2 : B ≤ 16 * ((⌈A⌉₊ : ℕ) : ℝ) :=
        le_trans hBA (mul_le_mul_of_nonneg_left hAN (by norm_num))
      have hb3 : ((⌊B⌋₊ : ℕ) : ℝ) ≤ ((⌈A⌉₊ * 16 : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hb3
  set N : ℕ := ⌈A⌉₊ with hNdef
  set M : ℕ := ⌊B⌋₊ with hMdef
  have hMN16 : M ≤ N * 16 := hMN
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  have hAN : A ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil A
  -- the coefficients
  set c : ℕ → ℂ := fun m => b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹
      * (m : ℂ)⁻¹ with hcdef
  set aa : ℕ → ℂ := fun n => if n ∈ Finset.Icc N M then (starRingEnd ℂ) (c n) else 0 with hadef
  have hsupp : ∀ n ∉ Finset.Icc N M, aa n = 0 := by
    intro n hn
    rw [hadef]
    exact if_neg hn
  have haa : ∀ n ∈ Finset.Icc N M, aa n = (starRingEnd ℂ) (c n) := by
    intro n hn
    rw [hadef]
    exact if_pos hn
  -- rewrite the remainder polynomial
  have hSR : ∀ r : Fin R, Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j (t r)
      = ∑ n ∈ Finset.Icc N M, c n * (n : ℂ) ^ (-(Complex.I * (t r : ℂ))) := by
    intro r
    rw [Work.BMF.mrDirect.remPolyR, Work.BMF.natIcc, ← hAdef, ← hBdef, ← hNdef, ← hMdef]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := le_trans (by exact_mod_cast hN1) hm.1
    have hm0 : (m : ℂ) ≠ 0 := by
      have hpos : (0 : ℕ) < m := hm1
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
    have hsplit : -((1 : ℂ) + Complex.I * (t r : ℂ))
        = -1 + -(Complex.I * (t r : ℂ)) := by ring
    rw [hsplit, Complex.cpow_add _ _ hm0, Complex.cpow_neg_one]
    simp only [hcdef]
    ring
  -- conjugation
  have hconj : ∀ r : Fin R,
      ‖∑ n ∈ Finset.Icc N M, c n * (n : ℂ) ^ (-(Complex.I * (t r : ℂ)))‖
        = ‖∑ n ∈ Finset.Icc N M, aa n * (n : ℂ) ^ (Complex.I * (t r : ℂ))‖ := by
    intro r
    have hconjEq :
        (starRingEnd ℂ) (∑ n ∈ Finset.Icc N M, c n * (n : ℂ) ^ (-(Complex.I * (t r : ℂ))))
          = ∑ n ∈ Finset.Icc N M, aa n * (n : ℂ) ^ (Complex.I * (t r : ℂ)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hz : (starRingEnd ℂ) (-(Complex.I * (t r : ℂ))) = Complex.I * (t r : ℂ) := by
        rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      rw [map_mul, conj_cpow_nat, hz, haa n hn]
    rw [← hconjEq, Complex.norm_conj]
  -- bound the coefficients
  have hcoef : ∀ n ∈ Finset.Icc N M, ‖aa n‖ ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by
    intro n hn
    have hmem := hn
    rw [haa n hn, Complex.norm_conj]
    rw [Finset.mem_Icc] at hmem
    have hn1 : 1 ≤ n := le_trans hN1 hmem.1
    have hcn : ‖c n‖ ≤ 1 / (n : ℝ) := by
      rw [hcdef]
      simp only
      rw [norm_mul, norm_mul]
      have hb1 : ‖b n‖ ≤ 1 := hb n
      have hω : ‖(((Work.BMF.mrDirect.omegaCount P Q n : ℕ) + 1 : ℕ) : ℂ)⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        have hk' : (1 : ℝ) ≤ ((Work.BMF.mrDirect.omegaCount P Q n + 1 : ℕ) : ℝ) := by
          have hle : (1 : ℕ) ≤ Work.BMF.mrDirect.omegaCount P Q n + 1 := Nat.le_add_left 1 _
          exact_mod_cast hle
        have hk'' : (1 : ℝ) ≤ ‖(((Work.BMF.mrDirect.omegaCount P Q n : ℕ) + 1 : ℕ) : ℂ)‖ := by
          rw [Complex.norm_natCast]
          exact hk'
        rw [inv_le_one₀ (by linarith)]
        exact hk''
      have hn' : ‖(n : ℂ)⁻¹‖ = 1 / (n : ℝ) := by
        rw [norm_inv, Complex.norm_natCast, one_div]
      calc ‖b n‖ * ‖(((Work.BMF.mrDirect.omegaCount P Q n : ℕ) + 1 : ℕ) : ℂ)⁻¹‖
            * ‖(n : ℂ)⁻¹‖
          ≤ 1 * 1 * (1 / (n : ℝ)) := by
            apply mul_le_mul (mul_le_mul hb1 hω (by positivity) (by norm_num))
              (le_of_eq hn') (by positivity) (by norm_num)
        _ = 1 / (n : ℝ) := by ring
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    calc ‖c n‖ ^ 2 ≤ (1 / (n : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcn 2
      _ = 1 / (n : ℝ) ^ 2 := by ring
  have hsum2 : (∑ n ∈ Finset.Icc N M, ‖aa n‖ ^ 2) ≤ 16 / A := by
    have h1 : (∑ n ∈ Finset.Icc N M, ‖aa n‖ ^ 2)
        ≤ ∑ n ∈ Finset.Icc N M, (1 : ℝ) / (n : ℝ) ^ 2 := Finset.sum_le_sum hcoef
    have h2 : (∑ n ∈ Finset.Icc N M, (1 : ℝ) / (n : ℝ) ^ 2) ≤ 16 / (N : ℝ) :=
      sum_inv_sq_Icc_le N M hN1 (by omega)
    have h3 : (16 : ℝ) / (N : ℝ) ≤ 16 / A := by
      have h := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < A) hAN
      calc (16 : ℝ) / (N : ℝ) = 16 * (1 / (N : ℝ)) := by ring
        _ ≤ 16 * (1 / A) := mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 16 / A := by ring
    linarith
  -- apply the sampled mean value bound
  have hsmv' := hsmv N M 16 aa TT R t hN1 (by norm_num) hTT (by omega) hsupp hIcc hsep
  have hmain : (∑ r, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j (t r)‖ ^ 2)
      = ∑ r, ‖∑ n ∈ Finset.Icc N M, aa n * (n : ℂ) ^ (Complex.I * (t r : ℂ))‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [hSR r, hconj r]
  rw [hmain]
  -- arithmetic
  have hEin : Real.exp (-((j : ℝ) + 1) / K) = (Real.exp (((j : ℝ) + 1) / K))⁻¹ := by
    have h1 : Real.exp (-((j : ℝ) + 1) / K) = Real.exp (-(((j : ℝ) + 1) / K)) := by
      congr 1
      ring
    rw [h1, Real.exp_neg]
  have hAB : 16 / A = 16 * Real.exp (((j : ℝ) + 1) / K) / X₁ := by
    rw [hAdef, hEin]
    field_simp <;> ring
  have hexp1 : Real.exp (((j : ℝ) + 1) / K)
      = Real.exp ((j : ℝ) / K) * Real.exp (1 / K) := by
    rw [← Real.exp_add]; congr 1; ring
  have h16A : 16 / A ≤ 64 * Real.exp ((j : ℝ) / K) / X₁ := by
    have hEq : 16 / A = 16 * (Real.exp ((j : ℝ) / K) * Real.exp (1 / K)) / X₁ := by
      rw [hAB, hexp1]
    calc 16 / A = 16 * (Real.exp ((j : ℝ) / K) * Real.exp (1 / K)) / X₁ := hEq
      _ ≤ 64 * Real.exp ((j : ℝ) / K) / X₁ := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hX₁pos)
          have h3 : Real.exp ((j : ℝ) / K) * Real.exp (1 / K)
              ≤ Real.exp ((j : ℝ) / K) * 4 :=
            mul_le_mul_of_nonneg_left hexpK (le_of_lt (Real.exp_pos _))
          nlinarith [h3, Real.exp_pos ((j : ℝ) / K)]
  have hM32 : (M : ℝ) ≤ 32 * A := by
    have h1 : (M : ℝ) ≤ 16 * (N : ℝ) := by
      have h0 : (M : ℝ) ≤ ((16 * N : ℕ) : ℝ) := by
        have hh : M ≤ 16 * N := by omega
        exact_mod_cast hh
      simpa using h0
    have hNlt : (N : ℝ) < A + 1 := by
      rw [hNdef]
      exact Nat.ceil_lt_add_one (by linarith)
    have h2 : (N : ℝ) ≤ 2 * A := by linarith [hNlt, hA1]
    calc (M : ℝ) ≤ 16 * (N : ℝ) := h1
      _ ≤ 16 * (2 * A) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 32 * A := by ring
  have hkey : (TT + (M : ℝ)) * (16 / A)
      ≤ 512 * (1 + TT * Real.exp ((j : ℝ) / K) / X₁) := by
    have h1 : (M : ℝ) * (16 / A) ≤ 512 := by
      have h3 : (M : ℝ) * (16 / A) ≤ 32 * A * (16 / A) :=
        mul_le_mul_of_nonneg_right hM32 (by positivity)
      have h4 : 32 * A * (16 / A) = 512 := by
        field_simp <;> ring
      linarith
    have h2 : TT * (16 / A) ≤ 256 * (TT * Real.exp ((j : ℝ) / K) / X₁) := by
      have h3 := mul_le_mul_of_nonneg_left h16A hTT
      have h4 : TT * (64 * Real.exp ((j : ℝ) / K) / X₁)
          ≤ 256 * (TT * Real.exp ((j : ℝ) / K) / X₁) := by
        have h5 : (0 : ℝ) ≤ TT * Real.exp ((j : ℝ) / K) / X₁ := by positivity
        rw [show TT * (64 * Real.exp ((j : ℝ) / K) / X₁)
            = 64 * (TT * Real.exp ((j : ℝ) / K) / X₁) by ring]
        linarith
      linarith
    have hsplit : (TT + (M : ℝ)) * (16 / A)
        = TT * (16 / A) + (M : ℝ) * (16 / A) := by ring
    have hfin : 256 * (TT * Real.exp ((j : ℝ) / K) / X₁) + 512
        ≤ 512 * (1 + TT * Real.exp ((j : ℝ) / K) / X₁) := by
      have h5 : (0 : ℝ) ≤ TT * Real.exp ((j : ℝ) / K) / X₁ := by positivity
      linarith
    linarith [hsplit, h1, h2, hfin]
  have hfin : Cs * (((16 : ℕ) : ℝ) + 1) * (TT + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖aa n‖ ^ 2)
      ≤ Cs * 17 * 512 * (1 + TT * Real.exp ((j : ℝ) / K) / X₁) := by
    have h2 : (TT + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖aa n‖ ^ 2)
        ≤ (TT + (M : ℝ)) * (16 / A) :=
      mul_le_mul_of_nonneg_left hsum2 (by positivity)
    calc Cs * (((16 : ℕ) : ℝ) + 1) * (TT + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖aa n‖ ^ 2)
        = Cs * 17 * ((TT + (M : ℝ)) * (∑ n ∈ Finset.Icc N M, ‖aa n‖ ^ 2)) := by ring
      _ ≤ Cs * 17 * ((TT + (M : ℝ)) * (16 / A)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Cs * 17 * (512 * (1 + TT * Real.exp ((j : ℝ) / K) / X₁)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = Cs * 17 * 512 * (1 + TT * Real.exp ((j : ℝ) / K) / X₁) := by ring
  exact le_trans hsmv' hfin


end

end Work.BMF.mr_direct
