import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.aesm_prod_comp_sub
import Submission.Work.BoseBoxFock.box_double_cauchy_schwarz
import Submission.Work.BoseBoxFock.box_prod_integrals
import Submission.Work.BoseBoxFock.errA_sq_int_le
import Submission.Work.BoseBoxFock.errBCD_sq_int_le
import Submission.Work.BoseBoxFock.err_aesm_bdd
import Submission.Work.BoseBoxFock.latPer_bdd_global
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The `θ = 1_Λ` factor has norm at most one. -/
lemma norm_thetaFun_le (ℓ : ℝ) (x : E3) : ‖Work.BoseK15.corpusBox.thetaFun ℓ x‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun]
  split <;> simp

/-- **Pointwise bound of the kernel difference** in terms of the four row errors. -/
lemma k1KerDiff_sq_le {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (Wa Wb : E3 → ℝ) (w y : E3) :
    ‖k1KerDiff v μ fu N Wa Wb w y‖ ^ 2
      ≤ 4 * (((ellH v μ) ^ 3)⁻¹) ^ 2 *
          (k1Chi ^ 2 * ‖k1ErrA v μ fu N Wa Wb (w - y)‖ ^ 2
            + k1Chi * ‖k1ErrB v μ fu N Wa Wb w‖ ^ 2
            + k1Chi * ‖k1ErrC v μ fu N Wa Wb y‖ ^ 2
            + ‖k1ErrD v μ fu N Wa Wb‖ ^ 2) := by
  rw [k1KerDiff, k1Kernel_decomp]
  set a : ℝ := ((ellH v μ) ^ 3)⁻¹ with ha
  set χw : ℝ := Submission.BoseGases.chiScale (ellH v μ) w with hχw
  set χy : ℝ := Submission.BoseGases.chiScale (ellH v μ) y with hχy
  set θw : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) w with hθw
  set θy : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) y with hθy
  set A : ℂ := k1ErrA v μ fu N Wa Wb (w - y) with hA
  set B : ℂ := k1ErrB v μ fu N Wa Wb w with hB
  set C : ℂ := k1ErrC v μ fu N Wa Wb y with hC
  set D : ℂ := k1ErrD v μ fu N Wa Wb with hD
  set T1 : ℂ := ((χw : ℝ) : ℂ) * ((χy : ℝ) : ℂ) * A with hT1
  set T2 : ℂ := ((χw : ℝ) : ℂ) * θy * B with hT2
  set T3 : ℂ := θw * ((χy : ℝ) : ℂ) * C with hT3
  set T4 : ℂ := θw * θy * D with hT4
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have ha0 : (0 : ℝ) < a := by rw [ha]; positivity
  have hχw2 : χw ^ 2 ≤ k1Chi := by
    rw [hχw]; exact chiScale_sq_le_k1Chi _ _
  have hχy2 : χy ^ 2 ≤ k1Chi := by
    rw [hχy]; exact chiScale_sq_le_k1Chi _ _
  have hθw1 : ‖θw‖ ≤ 1 := by rw [hθw]; exact norm_thetaFun_le _ _
  have hθy1 : ‖θy‖ ≤ 1 := by rw [hθy]; exact norm_thetaFun_le _ _
  have hχw_norm : ‖((χw : ℝ) : ℂ)‖ = χw := by
    have h : ‖((χw : ℝ) : ℂ)‖ = |χw| := by simp
    rw [h, abs_of_nonneg]
    rw [hχw]
    exact Submission.BoseGases.chi_nonneg _
  have hχy_norm : ‖((χy : ℝ) : ℂ)‖ = χy := by
    have h : ‖((χy : ℝ) : ℂ)‖ = |χy| := by simp
    rw [h, abs_of_nonneg]
    rw [hχy]
    exact Submission.BoseGases.chi_nonneg _
  have hK : (0 : ℝ) < k1Chi := k1Chi_pos
  have hb1 : ‖T1‖ ^ 2 ≤ k1Chi ^ 2 * ‖A‖ ^ 2 := by
    have h1 : ‖T1‖ = χw * χy * ‖A‖ := by
      rw [hT1, norm_mul, norm_mul, hχw_norm, hχy_norm]
    rw [h1, mul_pow, mul_pow]
    calc χw ^ 2 * χy ^ 2 * ‖A‖ ^ 2 ≤ k1Chi * k1Chi * ‖A‖ ^ 2 := by
          refine mul_le_mul (mul_le_mul hχw2 hχy2 (sq_nonneg _) hK.le) le_rfl (sq_nonneg _)
            (by positivity)
      _ = k1Chi ^ 2 * ‖A‖ ^ 2 := by ring
  have hb2 : ‖T2‖ ^ 2 ≤ k1Chi * ‖B‖ ^ 2 := by
    have h1 : ‖T2‖ = χw * ‖θy‖ * ‖B‖ := by
      rw [hT2, norm_mul, norm_mul, hχw_norm]
    have hθy2 : ‖θy‖ ^ 2 ≤ 1 := by
      have h := mul_le_mul hθy1 hθy1 (norm_nonneg θy) (by norm_num : (0 : ℝ) ≤ 1)
      simpa [pow_two] using h
    rw [h1, mul_pow, mul_pow]
    calc χw ^ 2 * ‖θy‖ ^ 2 * ‖B‖ ^ 2 ≤ k1Chi * 1 * ‖B‖ ^ 2 := by
          refine mul_le_mul (mul_le_mul hχw2 hθy2 (sq_nonneg _) hK.le) le_rfl (sq_nonneg _)
            (by positivity)
      _ = k1Chi * ‖B‖ ^ 2 := by ring
  have hb3 : ‖T3‖ ^ 2 ≤ k1Chi * ‖C‖ ^ 2 := by
    have h1 : ‖T3‖ = ‖θw‖ * χy * ‖C‖ := by
      rw [hT3, norm_mul, norm_mul, hχy_norm]
    have hθw2 : ‖θw‖ ^ 2 ≤ 1 := by
      have h := mul_le_mul hθw1 hθw1 (norm_nonneg θw) (by norm_num : (0 : ℝ) ≤ 1)
      simpa [pow_two] using h
    rw [h1, mul_pow, mul_pow]
    calc ‖θw‖ ^ 2 * χy ^ 2 * ‖C‖ ^ 2 ≤ 1 * k1Chi * ‖C‖ ^ 2 := by
          refine mul_le_mul (mul_le_mul hθw2 hχy2 (sq_nonneg _) (by norm_num)) le_rfl
            (sq_nonneg _) (by positivity)
      _ = k1Chi * ‖C‖ ^ 2 := by ring
  have hb4 : ‖T4‖ ^ 2 ≤ ‖D‖ ^ 2 := by
    have h1 : ‖T4‖ = ‖θw‖ * ‖θy‖ * ‖D‖ := by
      rw [hT4, norm_mul, norm_mul]
    have hθw2 : ‖θw‖ ^ 2 ≤ 1 := by
      have h := mul_le_mul hθw1 hθw1 (norm_nonneg θw) (by norm_num : (0 : ℝ) ≤ 1)
      simpa [pow_two] using h
    have hθy2 : ‖θy‖ ^ 2 ≤ 1 := by
      have h := mul_le_mul hθy1 hθy1 (norm_nonneg θy) (by norm_num : (0 : ℝ) ≤ 1)
      simpa [pow_two] using h
    rw [h1, mul_pow, mul_pow]
    calc ‖θw‖ ^ 2 * ‖θy‖ ^ 2 * ‖D‖ ^ 2 ≤ 1 * 1 * ‖D‖ ^ 2 := by
          refine mul_le_mul (mul_le_mul hθw2 hθy2 (sq_nonneg _) (by norm_num)) le_rfl
            (sq_nonneg _) (by positivity)
      _ = ‖D‖ ^ 2 := by ring
  have hS : ‖T1 - T2 - T3 + T4‖ ^ 2
      ≤ 4 * (‖T1‖ ^ 2 + ‖T2‖ ^ 2 + ‖T3‖ ^ 2 + ‖T4‖ ^ 2) := by
    have h1 : ‖T1 - T2 - T3 + T4‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ := by
      calc ‖T1 - T2 - T3 + T4‖ ≤ ‖T1 - T2 - T3‖ + ‖T4‖ := norm_add_le _ _
        _ ≤ (‖T1 - T2‖ + ‖T3‖) + ‖T4‖ := by
            linarith [norm_sub_le (T1 - T2) T3]
        _ ≤ ((‖T1‖ + ‖T2‖) + ‖T3‖) + ‖T4‖ := by
            linarith [norm_sub_le T1 T2]
    have hsq3 : (‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖) ^ 2
        ≤ 4 * (‖T1‖ ^ 2 + ‖T2‖ ^ 2 + ‖T3‖ ^ 2 + ‖T4‖ ^ 2) := by
      nlinarith [sq_nonneg (‖T1‖ - ‖T2‖), sq_nonneg (‖T1‖ - ‖T3‖), sq_nonneg (‖T1‖ - ‖T4‖),
        sq_nonneg (‖T2‖ - ‖T3‖), sq_nonneg (‖T2‖ - ‖T4‖), sq_nonneg (‖T3‖ - ‖T4‖)]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) hsq3
  have ha_norm : ‖((a : ℝ) : ℂ)‖ = a := by
    have h : ‖((a : ℝ) : ℂ)‖ = |a| := by simp
    rw [h, abs_of_pos ha0]
  rw [norm_mul, ha_norm]
  calc (a * ‖T1 - T2 - T3 + T4‖) ^ 2
      = a ^ 2 * ‖T1 - T2 - T3 + T4‖ ^ 2 := by ring
    _ ≤ a ^ 2 * (4 * (‖T1‖ ^ 2 + ‖T2‖ ^ 2 + ‖T3‖ ^ 2 + ‖T4‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hS (sq_nonneg a)
    _ ≤ 4 * a ^ 2 * (k1Chi ^ 2 * ‖A‖ ^ 2 + k1Chi * ‖B‖ ^ 2 + k1Chi * ‖C‖ ^ 2
          + ‖D‖ ^ 2) := by
        have ha2 : (0:ℝ) ≤ a ^ 2 := sq_nonneg a
        nlinarith [hb1, hb2, hb3, hb4, ha2, norm_nonneg A, norm_nonneg B, norm_nonneg C,
          norm_nonneg D, k1Chi_pos.le]


/-- **The `L²` bound of the kernel difference** from the four integrated row bounds.

This is the assembly step: the pointwise decomposition `k1KerDiff_sq_le` is integrated against
the product measure `μ ⊗ μ`, `μ = volume.restrict (boxL ℓ)`, and the four pieces are evaluated by
the fold identity for periodic functions and the two elementary Fubini computations
(`box_prod_integrals`). -/
lemma k1KerDiff_sq_int_le {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    {Wa Wb : E3 → ℝ} {δA δB δC δD : ℝ}
    (hI1 : Integrable (fun p : E3 × E3 => ‖k1ErrA v μ fu N Wa Wb (p.1 - p.2)‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hI2 : Integrable (fun p : E3 × E3 => ‖k1ErrB v μ fu N Wa Wb p.1‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hI3 : Integrable (fun p : E3 × E3 => ‖k1ErrC v μ fu N Wa Wb p.2‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hI4 : Integrable (fun p : E3 × E3 => ‖k1KerDiff v μ fu N Wa Wb p.1 p.2‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hI5 : Integrable (fun p : E3 × E3 =>
        4 * (((ellH v μ) ^ 3)⁻¹) ^ 2 *
          (k1Chi ^ 2 * ‖k1ErrA v μ fu N Wa Wb (p.1 - p.2)‖ ^ 2
            + k1Chi * ‖k1ErrB v μ fu N Wa Wb p.1‖ ^ 2
            + k1Chi * ‖k1ErrC v μ fu N Wa Wb p.2‖ ^ 2
            + ‖k1ErrD v μ fu N Wa Wb‖ ^ 2))
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hfold : ∀ {F : E3 → ℂ}, AEStronglyMeasurable F volume →
        (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
        (∀ (m : Fin 3 → ℤ) (z : E3), F (z + ellH v μ • latVec m) = F z) →
      (∫ p : E3 × E3, ‖F (p.1 - p.2)‖ ^ 2
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
        = (ellH v μ) ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖F z‖ ^ 2)
    (hfst : ∀ {F : E3 → ℂ}, AEStronglyMeasurable F volume →
        (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
      (∫ p : E3 × E3, ‖F p.1‖ ^ 2
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
        = (ellH v μ) ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖F z‖ ^ 2)
    (hsnd : ∀ {F : E3 → ℂ}, AEStronglyMeasurable F volume →
        (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
      (∫ p : E3 × E3, ‖F p.2‖ ^ 2
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
        = (ellH v μ) ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖F z‖ ^ 2)
    (hconst : ∀ c : ℝ, (∫ p : E3 × E3, c
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
        = c * (ellH v μ) ^ 6)
    (hA : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ‖k1ErrA v μ fu N Wa Wb z‖ ^ 2) ≤ δA)
    (hB : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ‖k1ErrB v μ fu N Wa Wb z‖ ^ 2) ≤ δB)
    (hC : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ‖k1ErrC v μ fu N Wa Wb z‖ ^ 2) ≤ δC)
    (hD : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ‖k1ErrD v μ fu N Wa Wb‖ ^ 2) ≤ δD)
    (hper : ∀ (m : Fin 3 → ℤ) (z : E3),
      k1ErrA v μ fu N Wa Wb (z + ellH v μ • latVec m) = k1ErrA v μ fu N Wa Wb z)
    (hAm : AEStronglyMeasurable (k1ErrA v μ fu N Wa Wb) volume)
    (hAb : ∃ C : ℝ, ∀ z, ‖k1ErrA v μ fu N Wa Wb z‖ ≤ C)
    (hBm : AEStronglyMeasurable (k1ErrB v μ fu N Wa Wb) volume)
    (hBb : ∃ C : ℝ, ∀ z, ‖k1ErrB v μ fu N Wa Wb z‖ ≤ C)
    (hCm : AEStronglyMeasurable (k1ErrC v μ fu N Wa Wb) volume)
    (hCb : ∃ C : ℝ, ∀ z, ‖k1ErrC v μ fu N Wa Wb z‖ ≤ C)
    (hI6 : Integrable (fun p : E3 × E3 => ‖k1ErrD v μ fu N Wa Wb‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hFub : (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ‖k1KerDiff v μ fu N Wa Wb w y‖ ^ 2)
      = ∫ p : E3 × E3, ‖k1KerDiff v μ fu N Wa Wb p.1 p.2‖ ^ 2
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))))) :
    (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ‖k1KerDiff v μ fu N Wa Wb w y‖ ^ 2)
      ≤ 4 * ((ellH v μ) ^ 3)⁻¹ * (k1Chi ^ 2 * δA + k1Chi * δB + k1Chi * δC + δD) := by
  rw [hFub]
  have hpt : ∀ p : E3 × E3, ‖k1KerDiff v μ fu N Wa Wb p.1 p.2‖ ^ 2
      ≤ 4 * (((ellH v μ) ^ 3)⁻¹) ^ 2 *
          (k1Chi ^ 2 * ‖k1ErrA v μ fu N Wa Wb (p.1 - p.2)‖ ^ 2
            + k1Chi * ‖k1ErrB v μ fu N Wa Wb p.1‖ ^ 2
            + k1Chi * ‖k1ErrC v μ fu N Wa Wb p.2‖ ^ 2
            + ‖k1ErrD v μ fu N Wa Wb‖ ^ 2) :=
    fun p => k1KerDiff_sq_le fu N Wa Wb p.1 p.2
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun p => by positivity) hI5
    (Filter.Eventually.of_forall hpt)
  have hP1 : Integrable (fun p : E3 × E3 => k1Chi ^ 2 * ‖k1ErrA v μ fu N Wa Wb (p.1 - p.2)‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := hI1.const_mul _
  have hP2 : Integrable (fun p : E3 × E3 => k1Chi * ‖k1ErrB v μ fu N Wa Wb p.1‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := hI2.const_mul _
  have hP3 : Integrable (fun p : E3 × E3 => k1Chi * ‖k1ErrC v μ fu N Wa Wb p.2‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := hI3.const_mul _
  have hP4 : Integrable (fun p : E3 × E3 => ‖k1ErrD v μ fu N Wa Wb‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := hI6
  have h1 := integral_add
    (f := fun p : E3 × E3 => k1Chi ^ 2 * ‖k1ErrA v μ fu N Wa Wb (p.1 - p.2)‖ ^ 2
      + k1Chi * ‖k1ErrB v μ fu N Wa Wb p.1‖ ^ 2
      + k1Chi * ‖k1ErrC v μ fu N Wa Wb p.2‖ ^ 2)
    (g := fun p : E3 × E3 => ‖k1ErrD v μ fu N Wa Wb‖ ^ 2)
    ((hP1.add hP2).add hP3) hP4
  have h2 := integral_add
    (f := fun p : E3 × E3 => k1Chi ^ 2 * ‖k1ErrA v μ fu N Wa Wb (p.1 - p.2)‖ ^ 2
      + k1Chi * ‖k1ErrB v μ fu N Wa Wb p.1‖ ^ 2)
    (g := fun p : E3 × E3 => k1Chi * ‖k1ErrC v μ fu N Wa Wb p.2‖ ^ 2)
    (hP1.add hP2) hP3
  have h3 := integral_add
    (f := fun p : E3 × E3 => k1Chi ^ 2 * ‖k1ErrA v μ fu N Wa Wb (p.1 - p.2)‖ ^ 2)
    (g := fun p : E3 × E3 => k1Chi * ‖k1ErrB v μ fu N Wa Wb p.1‖ ^ 2) hP1 hP2
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul]
  rw [h1, h2, h3]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  rw [hfold hAm hAb hper, hfst hBm hBb, hsnd hCm hCb, hconst]
  set IA := (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖k1ErrA v μ fu N Wa Wb z‖ ^ 2)
    with hIA
  set IB := (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖k1ErrB v μ fu N Wa Wb z‖ ^ 2)
    with hIB
  set IC := (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖k1ErrC v μ fu N Wa Wb z‖ ^ 2)
    with hIC
  have hA' : IA ≤ δA := hA
  have hB' : IB ≤ δB := hB
  have hC' : IC ≤ δC := hC
  have hℓ : (0 : ℝ) < ellH v μ := ellH_pos v μ
  have hℓ3 : (0 : ℝ) < (ellH v μ) ^ 3 := by positivity
  have hID : ‖k1ErrD v μ fu N Wa Wb‖ ^ 2 * (ellH v μ) ^ 6 ≤ (ellH v μ) ^ 3 * δD := by
    have h2 : (ellH v μ) ^ 3 * ‖k1ErrD v μ fu N Wa Wb‖ ^ 2 ≤ δD := by
      have h3 := hD
      rwa [setIntegral_const, volume_real_boxL hℓ, smul_eq_mul] at h3
    nlinarith [h2, hℓ3]
  have hID' : ‖k1ErrD v μ fu N Wa Wb‖ ^ 2 * (ellH v μ) ^ 3 ≤ δD := by
    have h2 : (ellH v μ) ^ 3 * (‖k1ErrD v μ fu N Wa Wb‖ ^ 2 * (ellH v μ) ^ 3)
        ≤ (ellH v μ) ^ 3 * δD := by
      nlinarith [hID]
    exact le_of_mul_le_mul_left h2 hℓ3
  have key : 4 * (((ellH v μ) ^ 3)⁻¹) ^ 2 *
        (k1Chi ^ 2 * ((ellH v μ) ^ 3 * IA) + k1Chi * ((ellH v μ) ^ 3 * IB)
          + k1Chi * ((ellH v μ) ^ 3 * IC) + ‖k1ErrD v μ fu N Wa Wb‖ ^ 2 * (ellH v μ) ^ 6)
      = 4 * ((ellH v μ) ^ 3)⁻¹ *
        (k1Chi ^ 2 * IA + k1Chi * IB + k1Chi * IC
          + ‖k1ErrD v μ fu N Wa Wb‖ ^ 2 * (ellH v μ) ^ 3) := by
    have hne : (ellH v μ) ^ 3 ≠ 0 := ne_of_gt hℓ3
    field_simp
  rw [key]
  have h1 : k1Chi ^ 2 * IA ≤ k1Chi ^ 2 * δA := mul_le_mul_of_nonneg_left hA' (by positivity)
  have h2 : k1Chi * IB ≤ k1Chi * δB := mul_le_mul_of_nonneg_left hB' k1Chi_pos.le
  have h3 : k1Chi * IC ≤ k1Chi * δC := mul_le_mul_of_nonneg_left hC' k1Chi_pos.le
  have hIA0 : 0 ≤ IA := by rw [hIA]; exact integral_nonneg (fun z => by positivity)
  have hIB0 : 0 ≤ IB := by rw [hIB]; exact integral_nonneg (fun z => by positivity)
  have hIC0 : 0 ≤ IC := by rw [hIC]; exact integral_nonneg (fun z => by positivity)
  have hδA : 0 ≤ δA := hIA0.trans hA'
  have hδB : 0 ≤ δB := hIB0.trans hB'
  have hδC : 0 ≤ δC := hIC0.trans hC'
  have hK0 : 0 ≤ k1Chi := k1Chi_pos.le
  have hID0 : 0 ≤ δD := (mul_nonneg (sq_nonneg _) hℓ3.le).trans hID'
  have hsum : k1Chi ^ 2 * IA + k1Chi * IB + k1Chi * IC
        + ‖k1ErrD v μ fu N Wa Wb‖ ^ 2 * (ellH v μ) ^ 3
      ≤ k1Chi ^ 2 * δA + k1Chi * δB + k1Chi * δC + δD := by
    linarith
  exact mul_le_mul_of_nonneg_left hsum (by positivity)


/-- Two points of the box have distance at most the diameter `√3 ℓ`. -/
lemma norm_sub_le_of_mem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {a b : E3}
    (ha : a ∈ Work.BoseK15.corpusBox.boxL ℓ) (hb : b ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    ‖a - b‖ ≤ Real.sqrt 3 * ℓ := by
  rw [corpusBox_boxL_eq_cell hℓ] at ha hb
  rw [Work.BoseFixR.mem_cell] at ha hb
  have h2 : ∑ i : Fin 3, ‖(a - b).ofLp i‖ ^ 2 ≤ 3 * ℓ ^ 2 := by
    have h3 : ∀ i : Fin 3, ‖(a - b).ofLp i‖ ^ 2 ≤ ℓ ^ 2 := by
      intro i
      have hai : |a i| ≤ ℓ / 2 := by simpa using ha i
      have hbi : |b i| ≤ ℓ / 2 := by simpa using hb i
      have h4 : |a i - b i| ≤ ℓ := by
        have h5 := abs_le.mp hai
        have h6 := abs_le.mp hbi
        rw [abs_le]
        exact ⟨by linarith [h5.1, h6.2], by linarith [h5.2, h6.1]⟩
      have h5 : ‖(a - b).ofLp i‖ = |a i - b i| := by simp
      rw [h5]
      nlinarith [abs_nonneg (a i - b i)]
    calc ∑ i : Fin 3, ‖(a - b).ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ℓ ^ 2 :=
          Finset.sum_le_sum fun i _ => h3 i
      _ = 3 * ℓ ^ 2 := by simp [Finset.sum_const]
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i : Fin 3, ‖(a - b).ofLp i‖ ^ 2) ≤ Real.sqrt (3 * ℓ ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = Real.sqrt 3 * ℓ := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq hℓ.le]


/-! ## The global boundedness of the first row error -/

lemma k1ErrA_bdd_global {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    {Wa Wb : E3 → ℝ} {Dp : ℝ}
    (hD : ∀ z : E3, ‖LatFourier.latPer (ellH v μ) (Wa + Wb) z‖ ≤ Dp)
    (hD0 : 0 ≤ Dp) :
    ∃ C : ℝ, ∀ z : E3, ‖k1ErrA v μ fu N Wa Wb z‖ ≤ C := by
  obtain ⟨Ba, hBa0, hBa⟩ := chat_abs_le_uniform (W := Wa)
  obtain ⟨Bb, hBb0, hBb⟩ := chat_abs_le_uniform (W := Wb)
  refine ⟨(Fintype.card (Lab N) : ℝ) * (Ba + Bb) + (ellH v μ) ^ 3 * Dp, fun z => ?_⟩
  have h1 : ‖pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z‖
      ≤ (Fintype.card (Lab N) : ℝ) * (Ba + Bb) := by
    calc ‖pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z‖
        ≤ ∑ k : Lab N, ‖(((k1cfun fu Wa Wb (ellH v μ) N k : ℝ)) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Lab N, (Ba + Bb) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul]
          have he : ‖Complex.exp (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ))‖ = 1 := by
            rw [mul_comm]
            exact Complex.norm_exp_ofReal_mul_I _
          rw [he, mul_one]
          have h2 : ‖(((k1cfun fu Wa Wb (ellH v μ) N k : ℝ)) : ℂ)‖
              = |k1cfun fu Wa Wb (ellH v μ) N k| := by simp
          rw [h2]
          have h3 : |k1cfun fu Wa Wb (ellH v μ) N k| ≤ Ba + Bb := by
            rw [k1cfun]
            have h7 := abs_add_le
              (uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
                * Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k))
              (Work.BoseFixR.chat Wb (kmomLab (ellH v μ) N k))
            have h8 : |uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
                * Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)| ≤ Ba := by
              rw [abs_mul]
              calc |uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)|
                    * |Work.BoseFixR.chat Wa (kmomLab (ellH v μ) N k)|
                  ≤ 1 * Ba := by
                    refine mul_le_mul ?_ (hBa _) (abs_nonneg _) (by norm_num)
                    rw [abs_of_nonneg (by rw [uvCut]; exact fu.nonneg _)]
                    rw [uvCut]
                    exact fu.le_one _
                _ = Ba := by ring
            linarith [h7, h8, hBb (kmomLab (ellH v μ) N k)]
          exact h3
      _ = (Fintype.card (Lab N) : ℝ) * (Ba + Bb) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h4 : ‖latPer3 (ellH v μ) (Wa + Wb) z‖ ≤ (ellH v μ) ^ 3 * Dp := by
    rw [latPer3, norm_mul]
    have h5 : ‖(((ellH v μ) ^ 3 : ℝ) : ℂ)‖ = (ellH v μ) ^ 3 := by
      have h6 : ‖(((ellH v μ) ^ 3 : ℝ) : ℂ)‖ = |(ellH v μ) ^ 3| := by simp
      rw [h6, abs_of_nonneg (by have hh := ellH_pos v μ; positivity : (0 : ℝ) ≤ (ellH v μ) ^ 3)]
    rw [h5]
    exact mul_le_mul_of_nonneg_left (hD z) (by have hh := ellH_pos v μ; positivity : (0 : ℝ) ≤ (ellH v μ) ^ 3)
  calc ‖k1ErrA v μ fu N Wa Wb z‖
      = ‖pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z
          - latPer3 (ellH v μ) (Wa + Wb) z‖ := rfl
    _ ≤ ‖pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z‖ + ‖latPer3 (ellH v μ) (Wa + Wb) z‖ :=
        norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h4

/-- The norm of a signed sum of four vectors is bounded by the sum of the bounds. -/
lemma norm_comb_le {E : Type*} [SeminormedAddCommGroup E] {a b c d : E} {ua ub uc ud : ℝ}
    (ha : ‖a‖ ≤ ua) (hb : ‖b‖ ≤ ub) (hc : ‖c‖ ≤ uc) (hd : ‖d‖ ≤ ud) :
    ‖a - b - c + d‖ ≤ ua + ub + uc + ud := by
  have h1 : ‖a - b - c + d‖ ≤ ‖a - b - c‖ + ‖d‖ := norm_add_le _ _
  have h2 : ‖a - b - c‖ ≤ ‖a - b‖ + ‖c‖ := norm_sub_le _ _
  have h3 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
  linarith

/-! ## The assembly of the pairing bound from the children -/

lemma k1_pairing_le_aux {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hWam : AEStronglyMeasurable Wa volume) (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C)
    (hWas : HasCompactSupport Wa) (hWae : ∀ z, Wa (-z) = Wa z)
    (hWbm : AEStronglyMeasurable Wb volume) (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C)
    (hWbs : HasCompactSupport Wb) (hWbe : ∀ z, Wb (-z) = Wb z)
    (hRowA : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖k1ErrA v μ fu N' Wa Wb z‖ ^ 2) ≤ ε)
    (hRowB : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖k1ErrB v μ fu N' Wa Wb z‖ ^ 2) ≤ ε)
    (hRowC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖k1ErrC v μ fu N' Wa Wb z‖ ^ 2) ≤ ε)
    (hRowD : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖k1ErrD v μ fu N' Wa Wb‖ ^ 2) ≤ ε)
    (hPkg : ∀ N : ℕ,
      (AEStronglyMeasurable (k1ErrA v μ fu N Wa Wb) volume ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖z‖ ≤ Real.sqrt 3 * ellH v μ →
          ‖k1ErrA v μ fu N Wa Wb z‖ ≤ C)
      ∧ (AEStronglyMeasurable (k1ErrB v μ fu N Wa Wb) volume ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖k1ErrB v μ fu N Wa Wb z‖ ≤ C)
      ∧ (AEStronglyMeasurable (k1ErrC v μ fu N Wa Wb) volume ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖k1ErrC v μ fu N Wa Wb z‖ ≤ C)
      ∧ (∃ C : ℝ, 0 ≤ C ∧ ‖k1ErrD v μ fu N Wa Wb‖ ≤ C))
    (hComp : ∀ (f : E3 → ℂ), AEStronglyMeasurable f volume → ∀ c : E3,
      AEStronglyMeasurable (fun p : E3 × E3 => f (p.1 - p.2 + c))
        ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
          (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hComp1 : ∀ (f : E3 → ℂ), AEStronglyMeasurable f volume →
      AEStronglyMeasurable (fun p : E3 × E3 => f p.1)
        ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
          (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hComp2 : ∀ (f : E3 → ℂ), AEStronglyMeasurable f volume →
      AEStronglyMeasurable (fun p : E3 × E3 => f p.2)
        ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
          (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
    (hDper : ∃ Dp : ℝ, 0 ≤ Dp ∧ ∀ z : E3,
      ‖LatFourier.latPer (ellH v μ) (Wa + Wb) z‖ ≤ Dp)
    (hFold : ∀ {F : E3 → ℂ}, AEStronglyMeasurable F volume → (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
      (∀ (m : Fin 3 → ℤ) (z : E3), F (z + ellH v μ • latVec m) = F z) →
      (∫ p : E3 × E3, ‖F (p.1 - p.2)‖ ^ 2
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
        = (ellH v μ) ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖F z‖ ^ 2)
    (hFst : ∀ {F : E3 → ℂ}, AEStronglyMeasurable F volume → (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
      (∫ p : E3 × E3, ‖F p.1‖ ^ 2
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
        = (ellH v μ) ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖F z‖ ^ 2)
    (hSnd : ∀ {F : E3 → ℂ}, AEStronglyMeasurable F volume → (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
      (∫ p : E3 × E3, ‖F p.2‖ ^ 2
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
        = (ellH v μ) ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖F z‖ ^ 2)
    (hConst : ∀ c : ℝ, (∫ p : E3 × E3, c
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))))
        = c * (ellH v μ) ^ 6)
    (hCS : ∀ {D G : E3 → E3 → ℂ},
      AEStronglyMeasurable (Function.uncurry D)
        ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
          (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) →
      AEStronglyMeasurable (Function.uncurry G)
        ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
          (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) →
      (∃ C : ℝ, ∀ w y, ‖D w y‖ ≤ C) → (∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C) →
      ‖∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ), D w y * G w y‖
        ≤ Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
              ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖D w y‖ ^ 2)
          * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
              ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖G w y‖ ^ 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      ∀ G : E3 → E3 → ℂ, Measurable (Function.uncurry G) →
        (∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C) →
        ‖∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
            ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
              k1KerDiff v μ fu N' Wa Wb w y * G w y‖
          ≤ ε * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
                ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖G w y‖ ^ 2) := by
  intro ε hε
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hboxm : MeasurableSet (Work.BoseK15.corpusBox.boxL (ellH v μ)) := by
    rw [corpusBox_boxL_eq_cell hℓ]
    exact Work.BoseFixR.measurableSet_boxL (ellH v μ)
  haveI : IsFiniteMeasure (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))) := by
    rw [MeasureTheory.isFiniteMeasure_restrict]
    rw [corpusBox_boxL_eq_cell hℓ, Work.BoseFixR.cell_eq_boxL, Work.BoseFixR.volume_boxL]
    exact ENNReal.ofReal_ne_top
  set Kt : ℝ := 4 * ((ellH v μ) ^ 3)⁻¹ * (k1Chi + 1) ^ 2 with hKt
  have hKt0 : 0 < Kt := by rw [hKt]; have := k1Chi_pos; positivity
  set δ : ℝ := ε ^ 2 / Kt with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨NA, hNA⟩ := hRowA δ hδ0
  obtain ⟨NB, hNB⟩ := hRowB δ hδ0
  obtain ⟨NC, hNC⟩ := hRowC δ hδ0
  obtain ⟨ND, hND⟩ := hRowD δ hδ0
  refine ⟨max (max NA NB) (max NC ND), fun N' hN' => ?_⟩
  have hN'A : NA ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN'
  have hN'B : NB ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN'
  have hN'C : NC ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN'
  have hN'D : ND ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN'
  intro G hGm hGbc
  obtain ⟨⟨hAm, hAb⟩, ⟨hBm, hBb⟩, ⟨hCm, hCb⟩, hDb⟩ := hPkg N'
  obtain ⟨CA, hCA0, hCAb⟩ := hAb
  obtain ⟨CB, hCB0, hCBb⟩ := hBb
  obtain ⟨CC, hCC0, hCCb⟩ := hCb
  obtain ⟨CD, hCD0, hCDb⟩ := hDb
  obtain ⟨Dp, hDp0, hDp⟩ := hDper
  have hAR : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
      ‖k1ErrA v μ fu N' Wa Wb z‖ ^ 2) ≤ δ := hNA N' hN'A
  have hBR : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
      ‖k1ErrB v μ fu N' Wa Wb z‖ ^ 2) ≤ δ := hNB N' hN'B
  have hCR : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
      ‖k1ErrC v μ fu N' Wa Wb z‖ ^ 2) ≤ δ := hNC N' hN'C
  have hDR : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
      ‖k1ErrD v μ fu N' Wa Wb‖ ^ 2) ≤ δ := hND N' hN'D
  have hmem : ∀ᵐ x ∂(volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))),
      x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
    rw [MeasureTheory.ae_restrict_iff' hboxm]
    exact Filter.Eventually.of_forall fun x hx => hx
  have hball : ∀ᵐ p ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
      (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))),
      p.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
        ∧ p.2 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      (p := fun q : E3 × E3 => q.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
        ∧ q.2 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)) (hboxm.prod hboxm)]
    filter_upwards [hmem] with x hx
    filter_upwards [hmem] with y hy
    exact ⟨hx, hy⟩
  have hErrA' : AEStronglyMeasurable (fun p : E3 × E3 => k1ErrA v μ fu N' Wa Wb (p.1 - p.2))
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := by
    simpa using hComp (k1ErrA v μ fu N' Wa Wb) hAm 0
  have hErrB' : AEStronglyMeasurable (fun p : E3 × E3 => k1ErrB v μ fu N' Wa Wb p.1)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
    hComp1 (k1ErrB v μ fu N' Wa Wb) hBm
  have hErrC' : AEStronglyMeasurable (fun p : E3 × E3 => k1ErrC v μ fu N' Wa Wb p.2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
    hComp2 (k1ErrC v μ fu N' Wa Wb) hCm
  have hI1 : Integrable (fun p : E3 × E3 => ‖k1ErrA v μ fu N' Wa Wb (p.1 - p.2)‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := by
    refine Integrable.of_bound ((continuous_norm.pow 2).comp_aestronglyMeasurable hErrA') (CA ^ 2) ?_
    exact hball.mono fun p hp => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCAb _ (norm_sub_le_of_mem_boxL hℓ hp.1 hp.2)) 2
  have hI2 : Integrable (fun p : E3 × E3 => ‖k1ErrB v μ fu N' Wa Wb p.1‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := by
    refine Integrable.of_bound ((continuous_norm.pow 2).comp_aestronglyMeasurable hErrB') (CB ^ 2) ?_
    exact hball.mono fun p _ => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCBb _) 2
  have hI3 : Integrable (fun p : E3 × E3 => ‖k1ErrC v μ fu N' Wa Wb p.2‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := by
    refine Integrable.of_bound ((continuous_norm.pow 2).comp_aestronglyMeasurable hErrC') (CC ^ 2) ?_
    exact hball.mono fun p _ => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCCb _) 2
  have hI6 : Integrable (fun p : E3 × E3 => ‖k1ErrD v μ fu N' Wa Wb‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
    integrable_const _
  have hI5 : Integrable (fun p : E3 × E3 =>
        4 * (((ellH v μ) ^ 3)⁻¹) ^ 2 *
          (k1Chi ^ 2 * ‖k1ErrA v μ fu N' Wa Wb (p.1 - p.2)‖ ^ 2
            + k1Chi * ‖k1ErrB v μ fu N' Wa Wb p.1‖ ^ 2
            + k1Chi * ‖k1ErrC v μ fu N' Wa Wb p.2‖ ^ 2
            + ‖k1ErrD v μ fu N' Wa Wb‖ ^ 2))
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := by
    have h := (((hI1.const_mul (k1Chi ^ 2)).add (hI2.const_mul k1Chi)).add
      (hI3.const_mul k1Chi)).add hI6
    exact h.const_mul _
  obtain ⟨CgA, hCgA⟩ := k1ErrA_bdd_global fu N' hDp hDp0
  set u : ℝ := Real.sqrt k1Chi with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = k1Chi := Real.sq_sqrt k1Chi_pos.le
  have hχ_le : ∀ x : E3, ‖((Submission.BoseGases.chiScale (ellH v μ) x : ℝ) : ℂ)‖ ≤ u := by
    intro x
    have h1 : ‖((Submission.BoseGases.chiScale (ellH v μ) x : ℝ) : ℂ)‖
        = |Submission.BoseGases.chiScale (ellH v μ) x| := by simp
    rw [h1]
    have h2 : Submission.BoseGases.chiScale (ellH v μ) x ^ 2 ≤ k1Chi :=
      chiScale_sq_le_k1Chi _ _
    nlinarith [abs_nonneg (Submission.BoseGases.chiScale (ellH v μ) x),
      sq_abs (Submission.BoseGases.chiScale (ellH v μ) x), hu2, hu0, h2]
  have hθ_le : ∀ x : E3, ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) x‖ ≤ 1 :=
    fun x => norm_thetaFun_le _ _
  have hKerBdd : ∃ C : ℝ, ∀ w y, ‖k1KerDiff v μ fu N' Wa Wb w y‖ ≤ C := by
    refine ⟨Real.sqrt (4 * (((ellH v μ) ^ 3)⁻¹) ^ 2 *
      (k1Chi ^ 2 * CgA ^ 2 + k1Chi * CB ^ 2 + k1Chi * CC ^ 2 + CD ^ 2)), fun w y => ?_⟩
    have h1 := k1KerDiff_sq_le (v := v) (μ := μ) fu N' Wa Wb w y
    have h2 : ‖k1KerDiff v μ fu N' Wa Wb w y‖ ^ 2
        ≤ 4 * (((ellH v μ) ^ 3)⁻¹) ^ 2 *
          (k1Chi ^ 2 * CgA ^ 2 + k1Chi * CB ^ 2 + k1Chi * CC ^ 2 + CD ^ 2) := by
      refine le_trans h1 ?_
      have h3 : ‖k1ErrA v μ fu N' Wa Wb (w - y)‖ ^ 2 ≤ CgA ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hCgA _) 2
      have h4 : ‖k1ErrB v μ fu N' Wa Wb w‖ ^ 2 ≤ CB ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hCBb w) 2
      have h5 : ‖k1ErrC v μ fu N' Wa Wb y‖ ^ 2 ≤ CC ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hCCb y) 2
      have h6 : ‖k1ErrD v μ fu N' Wa Wb‖ ^ 2 ≤ CD ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hCDb 2
      have hsum : k1Chi ^ 2 * ‖k1ErrA v μ fu N' Wa Wb (w - y)‖ ^ 2
            + k1Chi * ‖k1ErrB v μ fu N' Wa Wb w‖ ^ 2
            + k1Chi * ‖k1ErrC v μ fu N' Wa Wb y‖ ^ 2
            + ‖k1ErrD v μ fu N' Wa Wb‖ ^ 2
          ≤ k1Chi ^ 2 * CgA ^ 2 + k1Chi * CB ^ 2 + k1Chi * CC ^ 2 + CD ^ 2 :=
        add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left h3 (sq_nonneg k1Chi))
          (mul_le_mul_of_nonneg_left h4 k1Chi_pos.le))
          (mul_le_mul_of_nonneg_left h5 k1Chi_pos.le)) h6
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    calc ‖k1KerDiff v μ fu N' Wa Wb w y‖
        = Real.sqrt (‖k1KerDiff v μ fu N' Wa Wb w y‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (4 * (((ellH v μ) ^ 3)⁻¹) ^ 2 *
            (k1Chi ^ 2 * CgA ^ 2 + k1Chi * CB ^ 2 + k1Chi * CC ^ 2 + CD ^ 2)) :=
          Real.sqrt_le_sqrt h2
  have hχc : Continuous (fun x : E3 => Submission.BoseGases.chiScale (ellH v μ) x) :=
    Submission.BoseGases.chi_continuous.comp (continuous_const_smul _)
  have hχ1 : AEStronglyMeasurable
      (fun p : E3 × E3 => ((Submission.BoseGases.chiScale (ellH v μ) p.1 : ℝ) : ℂ))
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
    (Complex.continuous_ofReal.comp (hχc.comp continuous_fst)).aestronglyMeasurable
  have hχ2 : AEStronglyMeasurable
      (fun p : E3 × E3 => ((Submission.BoseGases.chiScale (ellH v μ) p.2 : ℝ) : ℂ))
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
    (Complex.continuous_ofReal.comp (hχc.comp continuous_snd)).aestronglyMeasurable
  have hθmeas : Measurable (Work.BoseK15.corpusBox.thetaFun (ellH v μ)) := by
    classical
    rw [show Work.BoseK15.corpusBox.thetaFun (ellH v μ)
        = fun x : E3 => if x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) then (1 : ℂ) else 0
        from rfl]
    exact Measurable.ite hboxm measurable_const measurable_const
  have hθ1 : AEStronglyMeasurable
      (fun p : E3 × E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
    (hθmeas.comp measurable_fst).aestronglyMeasurable
  have hθ2 : AEStronglyMeasurable
      (fun p : E3 × E3 => Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
    (hθmeas.comp measurable_snd).aestronglyMeasurable
  have hKerAesm : AEStronglyMeasurable (Function.uncurry (k1KerDiff v μ fu N' Wa Wb))
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := by
    have hdecomp : Function.uncurry (k1KerDiff v μ fu N' Wa Wb)
        = fun p : E3 × E3 => ((ellH v μ) ^ 3)⁻¹ *
            (((Submission.BoseGases.chiScale (ellH v μ) p.1 : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale (ellH v μ) p.2 : ℝ) : ℂ)
              * k1ErrA v μ fu N' Wa Wb (p.1 - p.2)
            - ((Submission.BoseGases.chiScale (ellH v μ) p.1 : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2 * k1ErrB v μ fu N' Wa Wb p.1
            - Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1
              * ((Submission.BoseGases.chiScale (ellH v μ) p.2 : ℝ) : ℂ)
              * k1ErrC v μ fu N' Wa Wb p.2
            + Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2
              * k1ErrD v μ fu N' Wa Wb) := by
      funext p
      exact k1Kernel_decomp (v := v) (μ := μ) fu N' Wa Wb p.1 p.2
    rw [hdecomp]
    have hDconst : AEStronglyMeasurable (fun _ : E3 × E3 => k1ErrD v μ fu N' Wa Wb)
        ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
          (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
      aestronglyMeasurable_const
    refine AEStronglyMeasurable.const_mul (AEStronglyMeasurable.add
      (AEStronglyMeasurable.sub (AEStronglyMeasurable.sub ?_ ?_) ?_) ?_) _
    · exact (hχ1.mul hχ2).mul hErrA'
    · exact (hχ1.mul hθ2).mul hErrB'
    · exact (hθ1.mul hχ2).mul hErrC'
    · exact (hθ1.mul hθ2).mul hDconst
  have hI4 : Integrable (fun p : E3 × E3 => ‖k1KerDiff v μ fu N' Wa Wb p.1 p.2‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) := by
    obtain ⟨Ck, hCk⟩ := hKerBdd
    refine Integrable.of_bound ((continuous_norm.pow 2).comp_aestronglyMeasurable hKerAesm) (Ck ^ 2) ?_
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCk p.1 p.2) 2
  have hFubKer : (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ‖k1KerDiff v μ fu N' Wa Wb w y‖ ^ 2)
      = ∫ p : E3 × E3, ‖k1KerDiff v μ fu N' Wa Wb p.1 p.2‖ ^ 2
          ∂((volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))).prod
              (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ)))) :=
    (MeasureTheory.integral_prod _ hI4).symm
  have hL2 := k1KerDiff_sq_int_le fu N' hI1 hI2 hI3 hI4 hI5 hFold hFst hSnd hConst
    hAR hBR hCR hDR (k1ErrA_periodic fu N' Wa Wb) hAm ⟨CgA, hCgA⟩ hBm ⟨CB, hCBb⟩
    hCm ⟨CC, hCCb⟩ hI6 hFubKer
  have hD2 : (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ‖k1KerDiff v μ fu N' Wa Wb w y‖ ^ 2) ≤ ε ^ 2 := by
    have hKtδ : Kt * δ = ε ^ 2 := by
      rw [hδ]
      field_simp
    refine le_trans hL2 ?_
    rw [show 4 * ((ellH v μ) ^ 3)⁻¹ *
          (k1Chi ^ 2 * δ + k1Chi * δ + k1Chi * δ + δ) = Kt * δ by
        rw [hKt]; ring]
    rw [hKtδ]
  have hcs := hCS hKerAesm hGm.aestronglyMeasurable hKerBdd hGbc
  refine le_trans hcs ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_iff.mpr ⟨hε.le, hD2⟩


/-- The `snd`-version of the two elementary Fubini computations of `box_prod_integrals` (the
landed sibling states the `fst` version; the product measure is symmetric). -/
lemma box_prod_snd {ℓ : ℝ} (hℓ : 0 < ℓ) {F : E3 → ℂ}
    (hFm : AEStronglyMeasurable F volume) (hFb : ∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) :
    (∫ p : E3 × E3, ‖F p.2‖ ^ 2
        ∂((volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
            (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))))
      = ℓ ^ 3 * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ‖F z‖ ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict]
    rw [corpusBox_boxL_eq_cell hℓ, Work.BoseFixR.cell_eq_boxL, Work.BoseFixR.volume_boxL]
    exact ENNReal.ofReal_ne_top
  have hInt : Integrable (fun p : E3 × E3 => ‖F p.2‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))) := by
    obtain ⟨C, hC⟩ := hFb
    refine Integrable.of_bound ((continuous_norm.pow 2).comp_aestronglyMeasurable ?_) (C ^ 2) ?_
    · rw [MeasureTheory.Measure.prod_restrict]
      exact (hFm.comp_snd (μ := volume)).mono_measure MeasureTheory.Measure.restrict_le_self
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC p.2) 2
  rw [MeasureTheory.integral_prod _ hInt]
  have hconst : ∀ x : E3, (∫ y : E3, ‖F y‖ ^ 2
      ∂(volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)))
      = ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ‖F z‖ ^ 2 := fun _ => rfl
  simp only [hconst]
  rw [MeasureTheory.integral_const, smul_eq_mul]
  congr 1
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply_univ]
  exact volume_real_boxL hℓ

/-- **FS's `Q₂`-row kernel truncation error**: the difference of the expanded pair kernel `K1exp`
and its limit `K1lim` is small in the `L²` pairing sense against any measurable bounded test kernel
`G` on the box. -/
theorem K1exp_sub_K1lim_pairing_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (fu : Work.BoseBoxFix.LowCut) {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWam : MeasureTheory.AEStronglyMeasurable Wa MeasureTheory.volume)
    (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C) (hWas : HasCompactSupport Wa)
    (hWae : ∀ z, Wa (-z) = Wa z)
    (hWbm : MeasureTheory.AEStronglyMeasurable Wb MeasureTheory.volume)
    (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C) (hWbs : HasCompactSupport Wb)
    (hWbe : ∀ z, Wb (-z) = Wb z) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
        Measurable (Function.uncurry G) →
        (∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C) →
        ‖∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
            ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
              (Work.BoseBoxFock.K1exp v μ N'
                  (fun k : Work.BoseBoxFock.Lab N' =>
                    Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N')
                      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N' k)
                      * Work.BoseFixR.chat Wa
                          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N' k)
                    + Work.BoseFixR.chat Wb (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N' k))
                  w y
                - Work.BoseBoxFock.K1lim (Work.BoseBoxFock.ellH v μ) (fun z => Wa z + Wb z) w y)
              * G w y‖
          ≤ ε * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
                ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ), ‖G w y‖ ^ 2) := by
  obtain ⟨Ra, hRa⟩ := k1ExistsRadius hWas
  obtain ⟨Rb, hRb⟩ := k1ExistsRadius hWbs
  have hRas : ∀ x : E3, max Ra Rb < ‖x‖ → Wa x = 0 :=
    fun x hx => hRa x (lt_of_le_of_lt (le_max_left _ _) hx)
  have hRbs : ∀ x : E3, max Ra Rb < ‖x‖ → Wb x = 0 :=
    fun x hx => hRb x (lt_of_le_of_lt (le_max_right _ _) hx)
  have hW0b : ∃ C : ℝ, ∀ x : E3, ‖(Wa + Wb) x‖ ≤ C := by
    obtain ⟨Ca, hCa⟩ := hWab
    obtain ⟨Cb, hCb⟩ := hWbb
    refine ⟨Ca + Cb, fun x => ?_⟩
    rw [Pi.add_apply]
    exact le_trans (norm_add_le _ _) (add_le_add (hCa x) (hCb x))
  have hW0s : ∀ x : E3, max Ra Rb < ‖x‖ → (Wa + Wb) x = 0 := fun x hx => by
    rw [Pi.add_apply, hRas x hx, hRbs x hx, add_zero]
  exact k1_pairing_le_aux fu hWam hWab hWas hWae hWbm hWbb hWbs hWbe
    (errA_sq_int_le fu hWam hWab hWas hWae hWbm hWbb hWbs hWbe)
    (errBCD_sq_int_le fu hWam hWab hWas hWbm hWbb hWbs).1
    (errBCD_sq_int_le fu hWam hWab hWas hWbm hWbb hWbs).2.1
    (errBCD_sq_int_le fu hWam hWab hWas hWbm hWbb hWbs).2.2
    (fun N => err_aesm_bdd fu N hWam hWab hWas hWbm hWbb hWbs)
    (fun f hf c => (aesm_prod_comp_sub (ellH_pos v μ) hf c).1)
    (fun f hf => (aesm_prod_comp_sub (ellH_pos v μ) hf 0).2.1)
    (fun f hf => (aesm_prod_comp_sub (ellH_pos v μ) hf 0).2.2)
    (latPer_bdd_global (ellH_pos v μ) hW0b hW0s)
    (box_prod_integrals (ellH_pos v μ)).1
    (box_prod_integrals (ellH_pos v μ)).2.1
    (box_prod_snd (ellH_pos v μ))
    (box_prod_integrals (ellH_pos v μ)).2.2
    (box_double_cauchy_schwarz (ellH_pos v μ))

end Work.BoseBoxFock
