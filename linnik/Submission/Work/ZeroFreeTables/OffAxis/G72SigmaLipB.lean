import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables

/-- **`Isub` is `208/105`-Lipschitz in `σ`.** -/
theorem G72SigmaLip (s σ τ : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |Work.ZeroFreeTables.OffAxis.Isub s σ - Work.ZeroFreeTables.OffAxis.Isub s τ|
      ≤ (208/105) * |σ - τ| := by
  have h1 : (G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I).re = -s := by simp
    have i1 : (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I).im = σ := by simp
    rw [e1, i1]
    simp only [neg_mul, neg_neg]
  have h2 : (G72 (((-s : ℝ) : ℂ) + (τ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (τ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((-s : ℝ) : ℂ) + (τ : ℂ) * Complex.I).re = -s := by simp
    have i1 : (((-s : ℝ) : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
    rw [e1, i1]
    simp only [neg_mul, neg_neg]
  have h3 : (G72 ((σ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((σ : ℂ) * Complex.I)).re = 0 := by simp
    have i1 : (((σ : ℂ) * Complex.I)).im = σ := by simp
    rw [e1, i1]
    simp
  have h4 : (G72 ((τ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((τ : ℂ) * Complex.I)).re = 0 := by simp
    have i1 : (((τ : ℂ) * Complex.I)).im = τ := by simp
    rw [e1, i1]
    simp
  have hdiff : Isub s σ - Isub s τ
      = ((∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y)
          - (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (τ*y) * g72 y))
        - 2 * ((∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y)
          - (∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y)) := by
    have e1 : Isub s σ
        = (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y)
          - 2 * (∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y) := by
      simp only [Isub]
      rw [h1, h3]
    have e2 : Isub s τ
        = (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (τ*y) * g72 y)
          - 2 * (∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y) := by
      simp only [Isub]
      rw [h2, h4]
    rw [e1, e2]
    ring
  have hc : ∀ y : ℝ, |Real.cos (σ*y) - Real.cos (τ*y)| ≤ (|σ - τ|) * |y| := by
    intro y
    have hh := Real.abs_cos_sub_cos_le (σ*y) (τ*y)
    rw [show σ*y - τ*y = (σ-τ)*y by ring, abs_mul] at hh
    exact hh
  have hA : |(∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y)
      - (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (τ*y) * g72 y)|
      ≤ (16/15) * |σ - τ| := by
    set F : ℝ → ℝ := fun y => Real.exp (s*y) * (Real.cos (σ*y) - Real.cos (τ*y)) * g72 y
      with hF
    have hi1 : IntervalIntegrable (fun y : ℝ => Real.exp (s*y) * Real.cos (σ*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    have hi2 : IntervalIntegrable (fun y : ℝ => Real.exp (s*y) * Real.cos (τ*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    have hsub : (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y)
        - (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (τ*y) * g72 y)
        = ∫ y in (0:ℝ)..2, F y := by
      rw [← intervalIntegral.integral_sub hi1 hi2]
      apply intervalIntegral.integral_congr
      intro y _
      simp only [hF]
      ring
    rw [hsub]
    have hnorm : |∫ y in (0:ℝ)..2, F y| ≤ ∫ y in (0:ℝ)..2, |F y| := by
      simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := 2) (f := F) (by norm_num)
    have hmono : (∫ y in (0:ℝ)..2, |F y|)
        ≤ ∫ y in (0:ℝ)..2, (|σ - τ|) * (y * Real.exp y * g72 y) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · apply Continuous.intervalIntegrable
        simp only [hF, Work.ZeroFreeTables.g72]
        fun_prop
      · apply Continuous.intervalIntegrable
        simp only [Work.ZeroFreeTables.g72]
        fun_prop
      · intro y hy
        have hy0 : 0 ≤ y := hy.1
        have hy2 : y ≤ 2 := hy.2
        have hg := g72_nonneg hy0 hy2
        have h1 : |Real.cos (σ*y) - Real.cos (τ*y)| ≤ (|σ - τ|) * y := by
          have hh := hc y
          rwa [abs_of_nonneg hy0] at hh
        have h2 : Real.exp (s*y) ≤ Real.exp y := Real.exp_le_exp.mpr (by nlinarith)
        simp only [hF]
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg hg]
        calc Real.exp (s*y) * |Real.cos (σ*y) - Real.cos (τ*y)| * g72 y
            ≤ Real.exp y * ((|σ-τ|) * y) * g72 y := by
              apply mul_le_mul_of_nonneg_right _ hg
              exact mul_le_mul h2 h1 (abs_nonneg _) (Real.exp_nonneg _)
          _ = (|σ-τ|) * (y * Real.exp y * g72 y) := by ring
    have hval : (∫ y in (0:ℝ)..2, (|σ-τ|) * (y * Real.exp y * g72 y))
        = (|σ-τ|) * (16/15) := by
      rw [intervalIntegral.integral_const_mul, integral_y_exp_g72]
    calc |∫ y in (0:ℝ)..2, F y| ≤ ∫ y in (0:ℝ)..2, |F y| := hnorm
      _ ≤ ∫ y in (0:ℝ)..2, (|σ-τ|) * (y * Real.exp y * g72 y) := hmono
      _ = (16/15) * |σ - τ| := by rw [hval]; ring
  have hB : |(∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y)
      - (∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y)| ≤ (16/35) * |σ - τ| := by
    set G : ℝ → ℝ := fun y => (Real.cos (σ*y) - Real.cos (τ*y)) * g72 y with hG
    have hi1 : IntervalIntegrable (fun y : ℝ => Real.cos (σ*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    have hi2 : IntervalIntegrable (fun y : ℝ => Real.cos (τ*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    have hsub : (∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y)
        - (∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y) = ∫ y in (0:ℝ)..2, G y := by
      rw [← intervalIntegral.integral_sub hi1 hi2]
      apply intervalIntegral.integral_congr
      intro y _
      simp only [hG]
      ring
    rw [hsub]
    have hnorm : |∫ y in (0:ℝ)..2, G y| ≤ ∫ y in (0:ℝ)..2, |G y| := by
      simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := 2) (f := G) (by norm_num)
    have hmono : (∫ y in (0:ℝ)..2, |G y|)
        ≤ ∫ y in (0:ℝ)..2, (|σ - τ|) * (y * g72 y) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · apply Continuous.intervalIntegrable
        simp only [hG, Work.ZeroFreeTables.g72]
        fun_prop
      · apply Continuous.intervalIntegrable
        simp only [Work.ZeroFreeTables.g72]
        fun_prop
      · intro y hy
        have hy0 : 0 ≤ y := hy.1
        have hy2 : y ≤ 2 := hy.2
        have hg := g72_nonneg hy0 hy2
        have h1 : |Real.cos (σ*y) - Real.cos (τ*y)| ≤ (|σ - τ|) * y := by
          have hh := hc y
          rwa [abs_of_nonneg hy0] at hh
        simp only [hG]
        rw [abs_mul, abs_of_nonneg hg]
        calc |Real.cos (σ*y) - Real.cos (τ*y)| * g72 y
            ≤ ((|σ-τ|) * y) * g72 y := mul_le_mul_of_nonneg_right h1 hg
          _ = (|σ-τ|) * (y * g72 y) := by ring
    have hval : (∫ y in (0:ℝ)..2, (|σ-τ|) * (y * g72 y)) = (|σ-τ|) * (16/35) := by
      rw [intervalIntegral.integral_const_mul, integral_y_g72]
    calc |∫ y in (0:ℝ)..2, G y| ≤ ∫ y in (0:ℝ)..2, |G y| := hnorm
      _ ≤ ∫ y in (0:ℝ)..2, (|σ-τ|) * (y * g72 y) := hmono
      _ = (16/35) * |σ - τ| := by rw [hval]; ring
  have hfin : |((∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y)
      - (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (τ*y) * g72 y))
      - 2 * ((∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y)
        - (∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y))| ≤ (208/105) * |σ - τ| := by
    have hB2 : |2 * ((∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y)
        - (∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y))| ≤ 2 * ((16/35) * |σ - τ|) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hB (by norm_num)
    have htri := abs_add_le
      ((∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y)
        - (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (τ*y) * g72 y))
      (-(2 * ((∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y)
        - (∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y))))
    rw [abs_neg] at htri
    rw [sub_eq_add_neg]
    linarith [htri, hA, hB2]
  calc |Isub s σ - Isub s τ|
      = |((∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y)
          - (∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (τ*y) * g72 y))
        - 2 * ((∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y)
          - (∫ y in (0:ℝ)..2, Real.cos (τ*y) * g72 y))| := by rw [hdiff]
    _ ≤ (208/105) * |σ - τ| := hfin

end Work.ZeroFreeTables.OffAxis
