import Mathlib
import Submission.Commons.Analysis.Integral.integrableOn_inv_norm_parabolic_ramp

open MeasureTheory Set Real
open scoped Interval InnerProductSpace

namespace Commons.Analysis.Integral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖cos θ • e + sin θ • f‖ = 1` for an orthonormal pair `e, f`. -/
private lemma norm_circVec_eq_one (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (θ : ℝ) :
    ‖Real.cos θ • e + Real.sin θ • f‖ = 1 := by
  have h : ‖Real.cos θ • e + Real.sin θ • f‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hef, mul_zero,
        norm_smul, norm_smul, he, hf, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [mul_one, mul_one, sq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (Real.cos θ • e + Real.sin θ • f), h]

/-- Integrability of `t ↦ (c t^{2/3} z)^{-1}` on `(0, T]`. -/
private lemma integrableOn_parA_inv_Ioc {c T z : ℝ} (hc : 0 < c) (hT : 0 < T) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => (c * t ^ ((2:ℝ)/3) * z)⁻¹) (Set.Ioc 0 T) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2:ℝ)/3)) (Set.Ioc (0:ℝ) T) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 : IntegrableOn (fun t : ℝ => (c * z)⁻¹ * t ^ (-(2:ℝ)/3)) (Set.Ioc (0:ℝ) T) :=
    hbase.const_mul _
  refine h2.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have e1 : t ^ (-(2:ℝ)/3) = (t ^ ((2:ℝ)/3))⁻¹ := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by ring, Real.rpow_neg ht0.le]
  rw [e1, show c * t ^ ((2:ℝ)/3) * z = (c * z) * t ^ ((2:ℝ)/3) by ring]
  simp only [mul_inv]

/-- Integrability of the `-‖A‖^{-1}` part on the rectangle. -/
private lemma integrableOn_parA_inv_prod {c T z : ℝ} (hc : 0 < c) (hT : 0 < T) (hz : 0 < z) :
    IntegrableOn (fun p : ℝ × ℝ => (c * p.2 ^ ((2:ℝ)/3) * z)⁻¹)
      (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.uIoc 0 T) := by
  have hT' : Integrable (fun t : ℝ => (c * t ^ ((2:ℝ)/3) * z)⁻¹)
      (volume.restrict (Set.uIoc 0 T)) := by
    rw [Set.uIoc_of_le hT.le]; exact integrableOn_parA_inv_Ioc hc hT hz
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    rw [isFiniteMeasure_restrict, Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi),
        Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hmain := hT'.comp_snd (volume.restrict (Set.uIoc 0 (2 * Real.pi)))
  rw [MeasureTheory.Measure.prod_restrict] at hmain
  exact hmain

/-- `min (min ρ T) X = min ρ X` for `X ≤ T`. -/
private lemma min_ramp_eq (ρ T X : ℝ) (hX : X ≤ T) : min (min ρ T) X = min ρ X := by
  rcases le_total ρ T with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, min_eq_right hX, min_eq_right (hX.trans h)]

/-- The main technical step: for `xi ≠ 0` and `ρ ≤ T`, the `θ`-parametric integral is
interval integrable. -/
private theorem intervalIntegrable_circle_gain_aux {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c T ρ : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ≤ T)
    (xi e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) (hxi : xi ≠ 0) :
    IntervalIntegrable (fun θ : ℝ => ∫ t in (0:ℝ)..T,
        (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) •
            (Real.cos θ • e + Real.sin θ • f)‖)⁻¹ - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹)
      MeasureTheory.volume 0 (2 * Real.pi) := by
  have hz : 0 < ‖xi‖ := norm_pos_iff.mpr hxi
  set S1 : Set ℝ := Set.Ioc 0 (2 * Real.pi) with hS1
  set S2 : Set ℝ := Set.Ioc 0 T with hS2
  have hA : Integrable (fun p : ℝ × ℝ => (‖(c * p.2 ^ ((2:ℝ)/3)) • xi
        + (min ρ (max 0 (T - p.2))) • (Real.cos p.1 • e + Real.sin p.1 • f)‖)⁻¹)
      ((volume.restrict S1).prod (volume.restrict S2)) := by
    have h := (integrableOn_inv_norm_parabolic_ramp e f xi he hf hef hc hT hρ hρT
      (rfl : ‖xi‖ = ‖xi‖) hz).integrable
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi), Set.uIoc_of_le hT.le,
        ← hS1, ← hS2] at h
    change Integrable _ ((volume.prod volume).restrict (S1 ×ˢ S2)) at h
    rw [← Measure.prod_restrict] at h
    exact h
  have hB : Integrable (fun p : ℝ × ℝ => (c * p.2 ^ ((2:ℝ)/3) * ‖xi‖)⁻¹)
      ((volume.restrict S1).prod (volume.restrict S2)) := by
    haveI : IsFiniteMeasure (volume.restrict S1) := by
      rw [hS1, isFiniteMeasure_restrict, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have hBt : Integrable (fun t : ℝ => (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹) (volume.restrict S2) := by
      rw [hS2]; exact integrableOn_parA_inv_Ioc hc hT hz
    exact hBt.comp_snd (volume.restrict S1)
  have hsub : Integrable (fun p : ℝ × ℝ => (‖(c * p.2 ^ ((2:ℝ)/3)) • xi
        + (min ρ (max 0 (T - p.2))) • (Real.cos p.1 • e + Real.sin p.1 • f)‖)⁻¹
        - (c * p.2 ^ ((2:ℝ)/3) * ‖xi‖)⁻¹)
      ((volume.restrict S1).prod (volume.restrict S2)) := hA.sub hB
  have hmarg := hsub.integral_prod_left
  have hfun : (fun θ : ℝ => ∫ t, (‖(c * t ^ ((2:ℝ)/3)) • xi
        + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
        - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹ ∂(volume.restrict S2))
      = (fun θ : ℝ => ∫ t in (0:ℝ)..T, (‖(c * t ^ ((2:ℝ)/3)) • xi
        + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
        - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹) := by
    funext θ
    rw [intervalIntegral.integral_of_le hT.le, ← hS2]
  rw [hfun] at hmarg
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi),
      ← hS1]
  change Integrable (fun θ : ℝ => ∫ t in (0:ℝ)..T, (‖(c * t ^ ((2:ℝ)/3)) • xi
        + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
        - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹) (volume.restrict S1)
  exact hmarg

theorem intervalIntegrable_circle_gain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c T ρ : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ) (xi e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    IntervalIntegrable (fun θ : ℝ => ∫ t in (0:ℝ)..T,
        (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) •
            (Real.cos θ • e + Real.sin θ • f)‖)⁻¹ - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹)
      MeasureTheory.volume 0 (2 * Real.pi) := by
  by_cases hxi : xi = 0
  · subst hxi
    have hpt : ∀ θ t : ℝ,
        (‖(c * t ^ ((2:ℝ)/3)) • (0:E) + (min ρ (max 0 (T - t))) •
            (Real.cos θ • e + Real.sin θ • f)‖)⁻¹ - (c * t ^ ((2:ℝ)/3) * ‖(0:E)‖)⁻¹
        = (min ρ (max 0 (T - t)))⁻¹ := by
      intro θ t
      have hb : 0 ≤ min ρ (max 0 (T - t)) := le_min hρ.le (le_max_left 0 _)
      simp only [norm_zero, smul_zero, zero_add]
      rw [norm_smul, norm_circVec_eq_one e f he hf hef θ, mul_one, Real.norm_eq_abs,
          abs_of_nonneg hb]
      simp
    have hfun : (fun θ : ℝ => ∫ t in (0:ℝ)..T,
        (‖(c * t ^ ((2:ℝ)/3)) • (0:E) + (min ρ (max 0 (T - t))) •
            (Real.cos θ • e + Real.sin θ • f)‖)⁻¹ - (c * t ^ ((2:ℝ)/3) * ‖(0:E)‖)⁻¹)
        = fun _ : ℝ => ∫ t in (0:ℝ)..T, (min ρ (max 0 (T - t)))⁻¹ := by
      funext θ
      exact intervalIntegral.integral_congr (fun t _ => hpt θ t)
    rw [hfun]
    exact intervalIntegrable_const
  · set ρ' : ℝ := min ρ T with hρ'_def
    have hρ'pos : 0 < ρ' := by rw [hρ'_def]; exact lt_min hρ hT
    have hρ'T : ρ' ≤ T := by rw [hρ'_def]; exact min_le_right _ _
    have haux := intervalIntegrable_circle_gain_aux hc hT hρ'pos hρ'T xi e f he hf hef hxi
    have hfun : (fun θ : ℝ => ∫ t in (0:ℝ)..T,
        (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) •
            (Real.cos θ • e + Real.sin θ • f)‖)⁻¹ - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹)
        = (fun θ : ℝ => ∫ t in (0:ℝ)..T,
        (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ' (max 0 (T - t))) •
            (Real.cos θ • e + Real.sin θ • f)‖)⁻¹ - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹) := by
      funext θ
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hT.le] at ht
      have hXt : max 0 (T - t) ≤ T := max_le hT.le (by linarith [ht.1])
      have hmin : min ρ' (max 0 (T - t)) = min ρ (max 0 (T - t)) := by
        rw [hρ'_def]; exact min_ramp_eq ρ T (max 0 (T - t)) hXt
      simp only [hmin]
    rw [hfun]
    exact haux

end Commons.Analysis.Integral
