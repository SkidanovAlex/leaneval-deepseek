import Mathlib
import Submission.Work.KMTAreas.A7.modBlockD2_eq_zero_of_one_lt

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open scoped BigOperators

noncomputable section

/-! ## Small norm facts -/

private lemma norm_two_complex : ‖(2 : ℂ)‖ = 2 := by
  have h : (2 : ℂ) = (((2 : ℝ)) : ℂ) := by norm_num
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  norm_num

private lemma norm_two_pi_I_mul (l : ℝ) :
    ‖(2 * Real.pi * Complex.I * (l : ℂ))‖ = 2 * Real.pi * |l| := by
  rw [show (2 * Real.pi * Complex.I * (l : ℂ))
        = (((2 * Real.pi * l : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos Real.pi_pos]

/-- Shifting the index of a sum over `range K` by one: the shifted sum is dominated by the sum
over `range (K+1)`, for a nonnegative summand. -/
private lemma sum_range_shift_le {f : ℕ → ℝ} (hf : ∀ n : ℕ, 0 ≤ f n) :
    ∀ K : ℕ, ∑ n ∈ Finset.range K, f (n + 1) ≤ ∑ i ∈ Finset.range (K + 1), f i
  | 0 => by simpa using hf 0
  | K + 1 => by
      have ih := sum_range_shift_le hf K
      rw [Finset.sum_range_succ (f := fun n => f (n + 1)) K,
        Finset.sum_range_succ (f := f) (K + 1)]
      linarith

/-! ## The expansion of `modBlockD2` -/

private lemma modBlockD2_expand (Φ : ℝ → ℂ) (s l ξ : ℝ) :
    modBlockD2 Φ s l ξ
      = (s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)
        + 2 * ((s * deriv Φ (s * ξ)) * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))
        + Φ (s * ξ) * ((2 * Real.pi * Complex.I * (l : ℂ))
            * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ))) := by
  simp only [modBlockD2]; ring

/-! ## The raw norm bound -/

private lemma norm_modBlockD2_le_raw {Φ : ℝ → ℂ} {M0 M1 M2 : ℝ}
    (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0) (hΦdb : ∀ u : ℝ, ‖deriv Φ u‖ ≤ M1)
    (hΦd2b : ∀ u : ℝ, ‖iteratedDeriv 2 Φ u‖ ≤ M2) (s l ξ : ℝ) :
    ‖modBlockD2 Φ s l ξ‖
      ≤ |s| ^ 2 * M2 + 4 * Real.pi * |s| * M1 * |l| + 4 * Real.pi ^ 2 * M0 * l ^ 2 := by
  have hAnorm : ‖(2 * Real.pi * Complex.I * (l : ℂ))‖ = 2 * Real.pi * |l| :=
    norm_two_pi_I_mul l
  have ht1 : ‖(s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)‖ ≤ |s| ^ 2 * M2 := by
    have hstep : ‖(s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)‖
        = |s| * (|s| * ‖iteratedDeriv 2 Φ (s * ξ)‖) := by
      simp only [norm_mul, norm_ee_eq_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hstep]
    have hb := hΦd2b (s * ξ)
    nlinarith [hb, norm_nonneg (iteratedDeriv 2 Φ (s * ξ)), abs_nonneg s]
  have ht2 : ‖2 * ((s * deriv Φ (s * ξ))
        * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖
      ≤ 4 * Real.pi * |s| * M1 * |l| := by
    have hstep : ‖2 * ((s * deriv Φ (s * ξ))
          * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖
        = ‖(2 : ℂ)‖ * ((|s| * ‖deriv Φ (s * ξ)‖) * (2 * Real.pi * |l|)) := by
      simp only [norm_mul, norm_ee_eq_one, mul_one, Complex.norm_real, Real.norm_eq_abs, hAnorm]
    rw [hstep, norm_two_complex]
    have hb := hΦdb (s * ξ)
    have hnn : (0 : ℝ) ≤ 2 * (|s| * (2 * Real.pi * |l|)) := by positivity
    have hprod := mul_le_mul_of_nonneg_left hb hnn
    nlinarith [hprod, norm_nonneg (deriv Φ (s * ξ)), abs_nonneg s, abs_nonneg l, Real.pi_pos]
  have ht3 : ‖Φ (s * ξ) * ((2 * Real.pi * Complex.I * (l : ℂ))
        * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖
      ≤ 4 * Real.pi ^ 2 * M0 * l ^ 2 := by
    have hstep : ‖Φ (s * ξ) * ((2 * Real.pi * Complex.I * (l : ℂ))
          * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖
        = ‖Φ (s * ξ)‖ * ((2 * Real.pi * |l|) * (2 * Real.pi * |l|)) := by
      simp only [norm_mul, norm_ee_eq_one, mul_one, hAnorm]
    rw [hstep]
    have hb := hΦb (s * ξ)
    have hP : (0 : ℝ) ≤ (2 * Real.pi * |l|) * (2 * Real.pi * |l|) := by positivity
    have hprod := mul_le_mul_of_nonneg_right hb hP
    have heq : M0 * ((2 * Real.pi * |l|) * (2 * Real.pi * |l|)) = 4 * Real.pi ^ 2 * M0 * l ^ 2 := by
      rw [show (2 * Real.pi * |l|) * (2 * Real.pi * |l|) = 4 * Real.pi ^ 2 * |l| ^ 2 by ring,
        sq_abs l]
      ring
    calc ‖Φ (s * ξ)‖ * ((2 * Real.pi * |l|) * (2 * Real.pi * |l|))
        ≤ M0 * ((2 * Real.pi * |l|) * (2 * Real.pi * |l|)) := hprod
      _ = 4 * Real.pi ^ 2 * M0 * l ^ 2 := heq
  rw [modBlockD2_expand]
  calc ‖(s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)
        + 2 * ((s * deriv Φ (s * ξ)) * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))
        + Φ (s * ξ) * ((2 * Real.pi * Complex.I * (l : ℂ))
            * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖
      ≤ ‖(s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)
          + 2 * ((s * deriv Φ (s * ξ))
              * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖
        + ‖Φ (s * ξ) * ((2 * Real.pi * Complex.I * (l : ℂ))
            * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖ := norm_add_le _ _
    _ ≤ (‖(s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)‖
          + ‖2 * ((s * deriv Φ (s * ξ))
              * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖)
        + ‖Φ (s * ξ) * ((2 * Real.pi * Complex.I * (l : ℂ))
            * ((2 * Real.pi * Complex.I * (l : ℂ)) * ee (l * ξ)))‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ |s| ^ 2 * M2 + 4 * Real.pi * |s| * M1 * |l| + 4 * Real.pi ^ 2 * M0 * l ^ 2 := by
        linarith [ht1, ht2, ht3]

/-! ## The pointwise `|ξ|²`-weighted bound -/

private lemma sq_norm_modBlockD2_le {Φ : ℝ → ℂ} {M0 M1 M2 cbar s l ξ : ℝ}
    (hcbar : 0 ≤ cbar) (hs : 0 ≤ s)
    (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0) (hΦdb : ∀ u : ℝ, ‖deriv Φ u‖ ≤ M1)
    (hΦd2b : ∀ u : ℝ, ‖iteratedDeriv 2 Φ u‖ ≤ M2)
    (hl : |l| ≤ cbar * s) (h1 : s * |ξ| ≤ 1) :
    |ξ| ^ 2 * ‖modBlockD2 Φ s l ξ‖
      ≤ (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2 * (s * |ξ|) := by
  have hM0 : 0 ≤ M0 := le_trans (norm_nonneg (Φ 0)) (hΦb 0)
  have hM1 : 0 ≤ M1 := le_trans (norm_nonneg (deriv Φ 0)) (hΦdb 0)
  have hM2 : 0 ≤ M2 := le_trans (norm_nonneg (iteratedDeriv 2 Φ 0)) (hΦd2b 0)
  have hpipos : 0 < Real.pi := Real.pi_pos
  set x : ℝ := s * |ξ| with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; exact mul_nonneg hs (abs_nonneg ξ)
  have hx1 : x ≤ 1 := by rw [hxdef]; exact h1
  have hx2 : x ^ 2 ≤ x := by nlinarith
  have hsab : |s| = s := abs_of_nonneg hs
  have hpart1 : |ξ| ^ 2 * (|s| ^ 2 * M2) ≤ M2 * x ^ 2 := by
    have heq : |ξ| ^ 2 * (|s| ^ 2 * M2) = M2 * x ^ 2 := by rw [hsab, hxdef]; ring
    exact heq.le
  have hpart2 : |ξ| ^ 2 * (4 * Real.pi * |s| * M1 * |l|) ≤ 4 * Real.pi * cbar * M1 * x ^ 2 := by
    have hcoef : 0 ≤ 4 * Real.pi * s * M1 := by positivity
    have hb : |ξ| ^ 2 * (4 * Real.pi * s * M1 * |l|)
        ≤ |ξ| ^ 2 * (4 * Real.pi * s * M1 * (cbar * s)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg |ξ|)
      exact mul_le_mul_of_nonneg_left hl hcoef
    have heq : |ξ| ^ 2 * (4 * Real.pi * s * M1 * (cbar * s))
        = 4 * Real.pi * cbar * M1 * x ^ 2 := by
      rw [hxdef]; ring
    calc |ξ| ^ 2 * (4 * Real.pi * |s| * M1 * |l|)
        = |ξ| ^ 2 * (4 * Real.pi * s * M1 * |l|) := by rw [hsab]
      _ ≤ |ξ| ^ 2 * (4 * Real.pi * s * M1 * (cbar * s)) := hb
      _ = 4 * Real.pi * cbar * M1 * x ^ 2 := heq
  have hpart3 : |ξ| ^ 2 * (4 * Real.pi ^ 2 * M0 * l ^ 2)
      ≤ 4 * Real.pi ^ 2 * cbar ^ 2 * M0 * x ^ 2 := by
    have hl2' : l ^ 2 ≤ cbar ^ 2 * s ^ 2 := by
      have h0 : (0 : ℝ) ≤ cbar * s + |l| := by linarith [hl, abs_nonneg l]
      have hprod := mul_le_mul_of_nonneg_right hl h0
      have hsq : |l| ^ 2 ≤ (cbar * s) ^ 2 := by nlinarith [hprod, hl, abs_nonneg l]
      calc l ^ 2 = |l| ^ 2 := (sq_abs l).symm
        _ ≤ (cbar * s) ^ 2 := hsq
        _ = cbar ^ 2 * s ^ 2 := by ring
    have hcoef : 0 ≤ 4 * Real.pi ^ 2 * M0 := by positivity
    have hb : |ξ| ^ 2 * (4 * Real.pi ^ 2 * M0 * l ^ 2)
        ≤ |ξ| ^ 2 * (4 * Real.pi ^ 2 * M0 * (cbar ^ 2 * s ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl2' hcoef) (sq_nonneg |ξ|)
    have heq : |ξ| ^ 2 * (4 * Real.pi ^ 2 * M0 * (cbar ^ 2 * s ^ 2))
        = 4 * Real.pi ^ 2 * cbar ^ 2 * M0 * x ^ 2 := by
      rw [hxdef]; ring
    calc |ξ| ^ 2 * (4 * Real.pi ^ 2 * M0 * l ^ 2)
        ≤ |ξ| ^ 2 * (4 * Real.pi ^ 2 * M0 * (cbar ^ 2 * s ^ 2)) := hb
      _ = 4 * Real.pi ^ 2 * cbar ^ 2 * M0 * x ^ 2 := heq
  have hK'nn : 0 ≤ M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0 := by
    have h1' : (0 : ℝ) ≤ 4 * Real.pi * cbar * M1 := by positivity
    have h2' : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * cbar ^ 2 * M0 := by positivity
    linarith
  have hK' : |ξ| ^ 2 * (|s| ^ 2 * M2 + 4 * Real.pi * |s| * M1 * |l| + 4 * Real.pi ^ 2 * M0 * l ^ 2)
      ≤ x ^ 2 * (M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0) := by
    have hsplit : |ξ| ^ 2 * (|s| ^ 2 * M2 + 4 * Real.pi * |s| * M1 * |l|
          + 4 * Real.pi ^ 2 * M0 * l ^ 2)
        = |ξ| ^ 2 * (|s| ^ 2 * M2) + |ξ| ^ 2 * (4 * Real.pi * |s| * M1 * |l|)
          + |ξ| ^ 2 * (4 * Real.pi ^ 2 * M0 * l ^ 2) := by ring
    rw [hsplit]
    linarith [hpart1, hpart2, hpart3]
  have hfinal : x ^ 2 * (M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0)
      ≤ (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2 * x := by
    have hstep : x ^ 2 * (M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0)
        ≤ x * (M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0) :=
      mul_le_mul_of_nonneg_right hx2 hK'nn
    have hc1 : cbar ≤ (1 + cbar) ^ 2 := by nlinarith [hcbar, sq_nonneg cbar]
    have hc2 : cbar ^ 2 ≤ (1 + cbar) ^ 2 := by nlinarith [hcbar, sq_nonneg cbar]
    have hc3 : (1 : ℝ) ≤ (1 + cbar) ^ 2 := by nlinarith [hcbar, sq_nonneg cbar]
    have e1 := mul_le_mul_of_nonneg_left hc3 hM2
    have e2 := mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * M1)
    have e3 := mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * M0)
    have hKle : M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0
        ≤ (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2 := by
      linarith [e1, e2, e3]
    calc x ^ 2 * (M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0)
        ≤ x * (M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0) := hstep
      _ ≤ x * ((M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2) :=
          mul_le_mul_of_nonneg_left hKle hx0
      _ = (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2 * x := by ring
  calc |ξ| ^ 2 * ‖modBlockD2 Φ s l ξ‖
      ≤ |ξ| ^ 2 * (|s| ^ 2 * M2 + 4 * Real.pi * |s| * M1 * |l| + 4 * Real.pi ^ 2 * M0 * l ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_modBlockD2_le_raw hΦb hΦdb hΦd2b s l ξ) (sq_nonneg |ξ|)
    _ ≤ x ^ 2 * (M2 + 4 * Real.pi * cbar * M1 + 4 * Real.pi ^ 2 * cbar ^ 2 * M0) := hK'
    _ ≤ (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2 * x := hfinal

/-! ## The real-valued lacunary sum bound -/

private lemma sum_lacunary_real_le {ι : Type*} {D : Finset ι} {σ : ι → ℝ} {lam : ℝ} (hlam : 1 < lam)
    (hlac : Work.Analysis.CzShift.LacunaryFam lam D σ) {ξ : ℝ} (hξ : ξ ≠ 0) {g : ι → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ i ∈ D, 0 ≤ g i)
    (hf : ∀ i ∈ D, σ i * |ξ| ≤ 1 → g i ≤ C * (σ i * |ξ|))
    (hzero : ∀ i ∈ D, 1 < σ i * |ξ| → g i = 0) :
    ∑ i ∈ D, g i ≤ 2 * C / (1 - lam⁻¹) := by
  have hmain : ∑ i ∈ D, ‖(((g i : ℝ)) : ℂ)‖ ≤ 2 * C / (1 - lam⁻¹) := by
    refine lacunarySum_norm_bound (D := D) (σ := σ) hlam hlac hξ
      (f := fun i => (((g i : ℝ)) : ℂ)) (C := C) hC ?_ ?_
    · intro i hi hle
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg i hi)]
      exact hf i hi hle
    · intro i hi hgt
      rw [hzero i hi hgt]
      simp
  have hkey : ∑ i ∈ D, ‖(((g i : ℝ)) : ℂ)‖ = ∑ i ∈ D, g i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg i hi)]
  rw [hkey] at hmain
  exact hmain

/-! ## The target theorem -/

theorem lacModDiff_deriv2_bound {Lam M0 M1 M2 : ℝ} (hLam : 1 < Lam) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2) {Φ : ℝ → ℂ} (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0)
    (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0)
    (hΦdb : ∀ u : ℝ, ‖deriv Φ u‖ ≤ M1) (hΦdsupp : ∀ u : ℝ, 1 ≤ |u| → deriv Φ u = 0)
    (hΦd2b : ∀ u : ℝ, ‖iteratedDeriv 2 Φ u‖ ≤ M2)
    (hΦd2supp : ∀ u : ℝ, 1 ≤ |u| → iteratedDeriv 2 Φ u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {cbar : ℝ}, 0 ≤ cbar →
      ∀ {sigma : ℕ → ℝ}, (∀ n : ℕ, 0 < sigma n) →
        (∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) →
      ∀ {lam : ℕ → ℝ}, (∀ n : ℕ, |lam n| ≤ cbar * sigma n) →
        (∀ n : ℕ, |lam (n + 1) - lam n| ≤ cbar * sigma n) →
      ∀ (K : ℕ) (eps : ℕ → ℂ), (∀ n : ℕ, ‖eps n‖ ≤ 1) → ∀ ξ : ℝ,
        |ξ| ^ 2 * ‖∑ n ∈ Finset.range K, eps n * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
          - modBlockD2 Φ (sigma n) (lam n) ξ)‖ ≤ C * (1 + cbar) ^ 2 := by
  have hLampos : 0 < Lam := lt_trans zero_lt_one hLam
  have hden : 0 < 1 - Lam⁻¹ := by
    have hinvpos : 0 < Lam⁻¹ := inv_pos.mpr hLampos
    have hone : Lam⁻¹ * Lam = 1 := inv_mul_cancel₀ (ne_of_gt hLampos)
    have hlt : Lam⁻¹ < 1 := by nlinarith [hLam, hinvpos, hone]
    linarith
  have hnum : 0 ≤ 4 * (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) := by positivity
  have hW : 0 ≤ 4 * (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) / (1 - Lam⁻¹) :=
    div_nonneg hnum hden.le
  refine ⟨4 * (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) / (1 - Lam⁻¹), hW, ?_⟩
  intro cbar hcbar sigma hsigma_pos hsigma_step lam hlam_bd hlam_diff K eps hε ξ
  have hC0 : (0 : ℝ) ≤ (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  rcases eq_or_ne ξ 0 with hξ0 | hξ0
  · rw [hξ0, abs_zero]
    have hz : ((0 : ℝ) ^ 2) = 0 := by norm_num
    rw [hz, zero_mul]
    exact mul_nonneg hW (sq_nonneg _)
  · have hf : ∀ i ∈ Finset.range (K + 1), sigma i * |ξ| ≤ 1 →
        |ξ| ^ 2 * ‖modBlockD2 Φ (sigma i) (lam i) ξ‖
          ≤ ((M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2)
              * (sigma i * |ξ|) :=
      fun i _ hle =>
        sq_norm_modBlockD2_le hcbar (hsigma_pos i).le hΦb hΦdb hΦd2b (hlam_bd i) hle
    have hzero : ∀ i ∈ Finset.range (K + 1), 1 < sigma i * |ξ| →
        |ξ| ^ 2 * ‖modBlockD2 Φ (sigma i) (lam i) ξ‖ = 0 := by
      intro i hi hgt
      rw [modBlockD2_eq_zero_of_one_lt hΦsupp hΦdsupp hΦd2supp (hsigma_pos i).le hgt]
      simp
    have hsum : ∑ i ∈ Finset.range (K + 1), |ξ| ^ 2 * ‖modBlockD2 Φ (sigma i) (lam i) ξ‖
        ≤ 2 * ((M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2)
            / (1 - Lam⁻¹) :=
      sum_lacunary_real_le hLam (lacunaryFam_range hLam hsigma_pos hsigma_step (K + 1)) hξ0 hC0
        (fun i _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)) hf hzero
    have hgnonneg : ∀ n : ℕ, 0 ≤ |ξ| ^ 2 * ‖modBlockD2 Φ (sigma n) (lam n) ξ‖ :=
      fun n => mul_nonneg (sq_nonneg _) (norm_nonneg _)
    have haux : |ξ| ^ 2 * ‖∑ n ∈ Finset.range K, eps n
          * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
          - modBlockD2 Φ (sigma n) (lam n) ξ)‖
        ≤ ∑ n ∈ Finset.range K, (|ξ| ^ 2 * ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ‖
            + |ξ| ^ 2 * ‖modBlockD2 Φ (sigma n) (lam n) ξ‖) := by
      have h1 : ‖∑ n ∈ Finset.range K, eps n * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
            - modBlockD2 Φ (sigma n) (lam n) ξ)‖
          ≤ ∑ n ∈ Finset.range K, (‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ‖
              + ‖modBlockD2 Φ (sigma n) (lam n) ξ‖) := by
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum (fun n _ => ?_)
        calc ‖eps n * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
              - modBlockD2 Φ (sigma n) (lam n) ξ)‖
            = ‖eps n‖ * ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
                - modBlockD2 Φ (sigma n) (lam n) ξ‖ := norm_mul _ _
          _ ≤ 1 * ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
                - modBlockD2 Φ (sigma n) (lam n) ξ‖ :=
              mul_le_mul_of_nonneg_right (hε n) (norm_nonneg _)
          _ = ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
                - modBlockD2 Φ (sigma n) (lam n) ξ‖ := one_mul _
          _ ≤ ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ‖
                + ‖modBlockD2 Φ (sigma n) (lam n) ξ‖ := norm_sub_le _ _
      calc |ξ| ^ 2 * ‖∑ n ∈ Finset.range K, eps n
            * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
            - modBlockD2 Φ (sigma n) (lam n) ξ)‖
          ≤ |ξ| ^ 2 * ∑ n ∈ Finset.range K, (‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ‖
              + ‖modBlockD2 Φ (sigma n) (lam n) ξ‖) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = ∑ n ∈ Finset.range K, (|ξ| ^ 2 * ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ‖
              + |ξ| ^ 2 * ‖modBlockD2 Φ (sigma n) (lam n) ξ‖) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun n _ => by ring)
    have hshift1 : ∑ n ∈ Finset.range K, |ξ| ^ 2 * ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ‖
        ≤ ∑ i ∈ Finset.range (K + 1), |ξ| ^ 2 * ‖modBlockD2 Φ (sigma i) (lam i) ξ‖ :=
      sum_range_shift_le hgnonneg K
    have hshift0 : ∑ n ∈ Finset.range K, |ξ| ^ 2 * ‖modBlockD2 Φ (sigma n) (lam n) ξ‖
        ≤ ∑ i ∈ Finset.range (K + 1), |ξ| ^ 2 * ‖modBlockD2 Φ (sigma i) (lam i) ξ‖ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ K))
        (fun i _ _ => hgnonneg i)
    calc |ξ| ^ 2 * ‖∑ n ∈ Finset.range K, eps n
          * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
          - modBlockD2 Φ (sigma n) (lam n) ξ)‖
        ≤ ∑ n ∈ Finset.range K, (|ξ| ^ 2 * ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ‖
            + |ξ| ^ 2 * ‖modBlockD2 Φ (sigma n) (lam n) ξ‖) := haux
      _ = (∑ n ∈ Finset.range K, |ξ| ^ 2 * ‖modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ‖)
            + (∑ n ∈ Finset.range K, |ξ| ^ 2 * ‖modBlockD2 Φ (sigma n) (lam n) ξ‖) :=
          Finset.sum_add_distrib
      _ ≤ (∑ i ∈ Finset.range (K + 1), |ξ| ^ 2 * ‖modBlockD2 Φ (sigma i) (lam i) ξ‖)
            + (∑ i ∈ Finset.range (K + 1), |ξ| ^ 2 * ‖modBlockD2 Φ (sigma i) (lam i) ξ‖) :=
          add_le_add hshift1 hshift0
      _ = 2 * ∑ i ∈ Finset.range (K + 1), |ξ| ^ 2 * ‖modBlockD2 Φ (sigma i) (lam i) ξ‖ := by ring
      _ ≤ 2 * (2 * ((M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) * (1 + cbar) ^ 2)
            / (1 - Lam⁻¹)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (4 * (M2 + 4 * Real.pi * M1 + 4 * Real.pi ^ 2 * M0) / (1 - Lam⁻¹)) * (1 + cbar) ^ 2 := by
          ring

end

end Work.KMTAreas.A7
