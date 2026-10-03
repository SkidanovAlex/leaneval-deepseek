/-
# `Work.FIArea3.JointCount.volume_argRegion_le`

The region `R = {z : ℂ | ‖z‖ ≤ b ∧ arg z ∈ [-γ, γ] ∧ re z < b·cos γ}` is (up to null sets) the
triangle with vertices `0`, `b·e^{iγ}`, `b·e^{-iγ}`, so its area equals `b² sin γ cos γ ≤ b²/2`.

The proof realises `R` as the image of the right triangle
`S = {w : ℂ | 0 ≤ re w ∧ 0 ≤ im w ∧ re w + im w ≤ b}` under the `ℝ`-linear map
`clc (cvec γ) (cvec (-γ)) : w ↦ re w • ⟨cos γ, sin γ⟩ + im w • ⟨cos γ, -sin γ⟩`,
whose determinant is `-2 sin γ cos γ`, of absolute value `sin (2γ) ≤ 1`.
Since `volume S = b²/2` (Fubini), the determinant formula gives `volume R ≤ volume S ≤ b²/2`.
-/
import Mathlib

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The `ℝ`-linear map `z ↦ z.re • u + z.im • v`. -/
private def clc (u v : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := z.re • u + z.im • v
  map_add' z w := by simp only [Complex.add_re, Complex.add_im, add_smul]; abel
  map_smul' r z := by simp only [Complex.smul_re, Complex.smul_im, smul_add, smul_smul,
    RingHom.id_apply, smul_eq_mul]

@[simp] private lemma clc_apply (u v z : ℂ) : clc u v z = z.re • u + z.im • v := rfl

private lemma clc_det (u v : ℂ) : LinearMap.det (clc u v) = u.re * v.im - v.re * u.im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI (clc u v), Matrix.det_fin_two]
  have h00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (clc u v)) 0 0 = u.re := by
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, clc]
  have h01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (clc u v)) 0 1 = v.re := by
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, clc]
  have h10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (clc u v)) 1 0 = u.im := by
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, clc]
  have h11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (clc u v)) 1 1 = v.im := by
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, clc]
  rw [h00, h01, h10, h11]

/-- The unit vector `⟨cos φ, sin φ⟩` at angle `φ`. -/
private def cvec (φ : ℝ) : ℂ := ⟨Real.cos φ, Real.sin φ⟩

@[simp] private lemma cvec_re (φ : ℝ) : (cvec φ).re = Real.cos φ := rfl
@[simp] private lemma cvec_im (φ : ℝ) : (cvec φ).im = Real.sin φ := rfl

/-- The area of the right triangle `{0 ≤ x, 0 ≤ y, x + y ≤ b} ⊆ ℝ²` equals `b²/2`. -/
private lemma volume_triangle_real (b : ℝ) (hb : 0 ≤ b) :
    MeasureTheory.volume {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ b}
      = ENNReal.ofReal (b^2/2) := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ b} := by measurability
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have step : ∀ x : ℝ, MeasureTheory.volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ b})
      = (Set.indicator (Set.Icc 0 b) (fun x => ENNReal.ofReal (b - x))) x := by
    intro x
    have hset : Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ b}
        = {y : ℝ | 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ b} := by ext y; simp
    rw [hset]
    by_cases hxb : x ∈ Set.Icc 0 b
    · have hset2 : {y : ℝ | 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ b} = Set.Icc 0 (b - x) := by
        ext y; simp only [Set.mem_ofPred_eq, mem_Icc]; constructor
        · intro h; exact ⟨h.2.1, by linarith [h.2.2]⟩
        · intro h; exact ⟨hxb.1, h.1, by linarith [h.2]⟩
      rw [hset2, Real.volume_Icc, Set.indicator_of_mem hxb]; norm_num
    · have hset2 : {y : ℝ | 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ b} = ∅ := by
        ext y
        simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro h
        rw [Set.mem_Icc, not_and_or, not_le] at hxb
        rcases hxb with hxb | hxb
        · exact absurd h.1 (not_le.mpr hxb)
        · exact absurd h.2.2 (not_le.mpr (by linarith [h.2.1, hxb]))
      rw [hset2, Set.indicator_of_notMem hxb]; simp
  rw [lintegral_congr step, MeasureTheory.lintegral_indicator measurableSet_Icc]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun a : ℝ => b - a)
        (μ := volume.restrict (Set.Icc 0 b)) ?hint ?hnn]
  · congr 1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb]
    rw [intervalIntegral.integral_comp_sub_left (f := fun y : ℝ => y) b, integral_id]; ring
  · exact (continuous_const.sub continuous_id).integrableOn_Icc
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with a ha
    exact sub_nonneg.mpr ha.2

/-- The area of the right triangle `{0 ≤ re w, 0 ≤ im w, re w + im w ≤ b} ⊆ ℂ` equals `b²/2`. -/
private lemma volume_triangle (b : ℝ) (hb : 0 ≤ b) :
    MeasureTheory.volume {w : ℂ | 0 ≤ w.re ∧ 0 ≤ w.im ∧ w.re + w.im ≤ b}
      = ENNReal.ofReal (b^2/2) := by
  have hset : Complex.measurableEquivRealProd ⁻¹'
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ b}
      = {w : ℂ | 0 ≤ w.re ∧ 0 ≤ w.im ∧ w.re + w.im ≤ b} := by
    ext w; simp [Complex.measurableEquivRealProd_apply]
  have hmeas : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ b} := by measurability
  have hpres : MeasureTheory.volume (Complex.measurableEquivRealProd ⁻¹'
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ b})
      = MeasureTheory.volume {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ b} :=
    Complex.volume_preserving_equiv_real_prod.measure_preimage hmeas.nullMeasurableSet
  rw [← hset, hpres]
  exact volume_triangle_real b hb

theorem volume_argRegion_le (b γ : ℝ) (hb : 0 ≤ b) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    (MeasureTheory.volume {z : ℂ | ‖z‖ ≤ b ∧ z.arg ∈ Set.Icc (-γ) γ ∧ z.re < b * Real.cos γ}).toReal
      ≤ b ^ 2 / 2 := by
  have hsub : {z : ℂ | ‖z‖ ≤ b ∧ z.arg ∈ Set.Icc (-γ) γ ∧ z.re < b * Real.cos γ}
      ⊆ clc (cvec γ) (cvec (-γ)) '' {w : ℂ | 0 ≤ w.re ∧ 0 ≤ w.im ∧ w.re + w.im ≤ b} := by
    rintro z ⟨hnorm, harg, hre_lt⟩
    have hre_ge : 0 ≤ z.re := by
      have h1 : |z.arg| ≤ Real.pi / 2 := by
        rw [abs_le]; exact ⟨by linarith [harg.1], by linarith [harg.2]⟩
      exact Complex.abs_arg_le_pi_div_two_iff.mp h1
    have hcosnn : 0 ≤ Real.cos γ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hγ1⟩
    by_cases hbcos : b * Real.cos γ = 0
    · exfalso; linarith [hre_ge, hre_lt, hbcos]
    · have hcos_pos : 0 < Real.cos γ := by
        by_contra h
        have h' : Real.cos γ ≤ 0 := not_lt.mp h
        have : b * Real.cos γ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb h'
        linarith
      rcases eq_or_lt_of_le hγ0 with hγeq | hγpos
      · subst hγeq
        have harg0 : z.arg = 0 := by simpa using harg
        have him0 : z.im = 0 := by
          have h := Complex.norm_mul_sin_arg z
          rw [harg0, Real.sin_zero, mul_zero] at h; exact h.symm
        refine ⟨(z.re : ℂ), ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · simpa using hre_ge
          · simp
          · simp only [Complex.ofReal_re, Complex.ofReal_im, add_zero]
            have h := hre_lt; rw [Real.cos_zero, mul_one] at h; linarith
        · rw [clc_apply]; apply Complex.ext <;> simp [cvec, him0]
      · have hsin_pos : 0 < Real.sin γ :=
          Real.sin_pos_of_pos_of_lt_pi hγpos (by linarith [hγ1, Real.pi_pos])
        have hsinγnn : 0 ≤ Real.sin γ := le_of_lt hsin_pos
        have hθ_abs : |z.arg| ≤ γ := abs_le.mpr ⟨harg.1, harg.2⟩
        have hcosθ : Real.cos γ ≤ Real.cos z.arg := by
          have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg z.arg)
            (by linarith [hγ1, Real.pi_pos]) hθ_abs
          rwa [Real.cos_abs] at h
        have hsinθ : |Real.sin z.arg| ≤ Real.sin γ := by
          rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [hθ_abs, hγ1, Real.pi_pos])]
          exact Real.sin_le_sin_of_le_of_le_pi_div_two
            (by linarith [abs_nonneg z.arg, Real.pi_pos]) hγ1 hθ_abs
        have hineq : |z.im| * Real.cos γ ≤ z.re * Real.sin γ := by
          have hA : |Real.sin z.arg| * Real.cos γ ≤ Real.sin γ * Real.cos z.arg :=
            calc |Real.sin z.arg| * Real.cos γ ≤ Real.sin γ * Real.cos γ :=
                  mul_le_mul_of_nonneg_right hsinθ hcosnn
              _ ≤ Real.sin γ * Real.cos z.arg := mul_le_mul_of_nonneg_left hcosθ hsinγnn
          rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z, abs_mul,
            abs_of_nonneg (norm_nonneg z)]
          nlinarith [hA, norm_nonneg z]
        refine ⟨Complex.mk ((z.re / Real.cos γ + z.im / Real.sin γ)/2)
            ((z.re / Real.cos γ - z.im / Real.sin γ)/2), ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · have h2 : 0 ≤ z.re * Real.sin γ + z.im * Real.cos γ := by
              have h1 : -(z.im) * Real.cos γ ≤ |z.im| * Real.cos γ :=
                mul_le_mul_of_nonneg_right (neg_le_abs z.im) hcosnn
              linarith [hineq, h1]
            have hnum : 0 ≤ z.re / Real.cos γ + z.im / Real.sin γ := by
              rw [div_add_div _ _ (ne_of_gt hcos_pos) (ne_of_gt hsin_pos)]
              exact div_nonneg (by linarith [h2]) (le_of_lt (mul_pos hcos_pos hsin_pos))
            exact div_nonneg hnum (by norm_num)
          · have h4 : 0 ≤ z.re * Real.sin γ - z.im * Real.cos γ := by
              have h3 : z.im * Real.cos γ ≤ |z.im| * Real.cos γ :=
                mul_le_mul_of_nonneg_right (le_abs_self z.im) hcosnn
              linarith [hineq, h3]
            have hnum : 0 ≤ z.re / Real.cos γ - z.im / Real.sin γ := by
              rw [div_sub_div z.re z.im (ne_of_gt hcos_pos) (ne_of_gt hsin_pos)]
              exact div_nonneg (by linarith [h4]) (le_of_lt (mul_pos hcos_pos hsin_pos))
            exact div_nonneg hnum (by norm_num)
          · have hsum : (z.re / Real.cos γ + z.im / Real.sin γ)/2
                + (z.re / Real.cos γ - z.im / Real.sin γ)/2 = z.re / Real.cos γ := by ring
            rw [hsum, div_le_iff₀ hcos_pos]; linarith [hre_lt]
        · rw [clc_apply]; apply Complex.ext
          · simp only [Complex.add_re, Complex.smul_re, cvec_re, Real.cos_neg, smul_eq_mul]
            field_simp; ring
          · simp only [Complex.add_im, Complex.smul_im, cvec_im, Real.sin_neg, smul_eq_mul]
            field_simp; ring
  have hdetreal : |LinearMap.det (clc (cvec γ) (cvec (-γ)))| ≤ 1 := by
    have hdet : LinearMap.det (clc (cvec γ) (cvec (-γ))) = - Real.sin (2 * γ) := by
      rw [clc_det, cvec_re, cvec_im, cvec_re, cvec_im, Real.cos_neg, Real.sin_neg, Real.sin_two_mul]
      ring
    rw [hdet, abs_neg, abs_of_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)]
    exact Real.sin_le_one _
  have hdetle : ENNReal.ofReal |LinearMap.det (clc (cvec γ) (cvec (-γ)))| ≤ 1 :=
    ENNReal.ofReal_le_one.mpr hdetreal
  have hvolS := volume_triangle b hb
  have hμ : MeasureTheory.volume {z : ℂ | ‖z‖ ≤ b ∧ z.arg ∈ Set.Icc (-γ) γ ∧ z.re < b * Real.cos γ}
      ≤ ENNReal.ofReal (b^2/2) := by
    calc MeasureTheory.volume {z : ℂ | ‖z‖ ≤ b ∧ z.arg ∈ Set.Icc (-γ) γ ∧ z.re < b * Real.cos γ}
        ≤ MeasureTheory.volume (clc (cvec γ) (cvec (-γ)) ''
            {w : ℂ | 0 ≤ w.re ∧ 0 ≤ w.im ∧ w.re + w.im ≤ b}) := measure_mono hsub
      _ = ENNReal.ofReal |LinearMap.det (clc (cvec γ) (cvec (-γ)))| *
            MeasureTheory.volume {w : ℂ | 0 ≤ w.re ∧ 0 ≤ w.im ∧ w.re + w.im ≤ b} :=
          MeasureTheory.Measure.addHaar_image_linearMap MeasureTheory.volume _ _
      _ = ENNReal.ofReal |LinearMap.det (clc (cvec γ) (cvec (-γ)))| * ENNReal.ofReal (b^2/2) := by
            rw [hvolS]
      _ ≤ 1 * ENNReal.ofReal (b^2/2) := by gcongr
      _ = ENNReal.ofReal (b^2/2) := one_mul _
  calc (MeasureTheory.volume {z : ℂ | ‖z‖ ≤ b ∧ z.arg ∈ Set.Icc (-γ) γ ∧ z.re < b * Real.cos γ}).toReal
      ≤ (ENNReal.ofReal (b^2/2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ
    _ = b^2/2 := ENNReal.toReal_ofReal (by positivity)

end

end Work.FIArea3.JointCount
