import Mathlib
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.UniformGap
import Submission.Work.Mostow.BusemannFormula

namespace Work.Mostow

open Submission.Mostow MeasureTheory

noncomputable section

theorem BaryCoercive (n : ℕ) (ν : MeasureTheory.Measure (Submission.Mostow.E n)) (hν : MeasureTheory.IsProbabilityMeasure ν) (hsupp : ν (Submission.Mostow.Sph n)ᶜ = 0)
    (hatom : ∀ ξ : Submission.Mostow.E n, ν {ξ} = 0) :
    ∃ R : ℝ, ∀ y : Submission.Mostow.E n, R ≤ Submission.Mostow.hdist 0 y → Submission.Mostow.baryFun ν 0 < Submission.Mostow.baryFun ν y := by
  haveI := hν
  have hGap : ∃ δ : ℝ, 0 < δ ∧ ∀ ŷ ∈ Sph n,
      (3/4 : ℝ) ≤ (ν {ξ : E n | δ ≤ 1 - inner ℝ ŷ ξ}).toReal :=
    UniformGap n ν hν hsupp hatom
  have hRay : ∀ (y ξ : E n), y ≠ 0 → ξ ∈ Sph n →
      busemann ξ y = -(hdist 0 y) + Real.log (1 + (1 - inner ℝ ((‖y‖)⁻¹ • y) ξ) *
        ((Real.exp (2 * hdist 0 y) - 1) / 2)) ∧ -(hdist 0 y) ≤ busemann ξ y :=
    fun y ξ hy hξ => BusemannFormula n y ξ hy hξ
  obtain ⟨δ₀, hδ₀pos, hδ₀gap⟩ := hGap
  set δ : ℝ := min δ₀ 1 with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min hδ₀pos one_pos
  have hδle1 : δ ≤ 1 := by rw [hδ]; exact min_le_right _ _
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hδgap : ∀ ŷ ∈ Sph n, (3/4 : ℝ) ≤ (ν {ξ : E n | δ ≤ 1 - inner ℝ ŷ ξ}).toReal := by
    intro ŷ hŷ
    have hsub : {ξ : E n | δ₀ ≤ 1 - inner ℝ ŷ ξ} ⊆ {ξ : E n | δ ≤ 1 - inner ℝ ŷ ξ} := by
      intro ξ hξ
      have hle : δ ≤ δ₀ := by rw [hδ]; exact min_le_left _ _
      exact le_trans hle hξ
    exact le_trans (hδ₀gap ŷ hŷ)
      (ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsub))
  refine ⟨max 1 ((3/2) * Real.log (2 / δ) + 1), ?_⟩
  intro y hyR
  have hRpos : 0 < max 1 ((3/2) * Real.log (2 / δ) + 1) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hy_ne : y ≠ 0 := by
    intro h
    rw [h, hdist_self] at hyR
    linarith [hRpos]
  set s : ℝ := hdist 0 y with hs
  have hsR : max 1 ((3/2) * Real.log (2 / δ) + 1) ≤ s := by rw [hs]; exact hyR
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hsR
  have hs0 : 0 ≤ s := by linarith
  have hlogR : (3/2) * Real.log (2 / δ) + 1 ≤ s := le_trans (le_max_right _ _) hsR
  have hynorm_ne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy_ne
  set ŷ : E n := (‖y‖)⁻¹ • y with hŷ
  have hŷSph : ŷ ∈ Sph n := by
    rw [mem_Sph_iff, hŷ, norm_smul, Real.norm_eq_abs, abs_inv]
    rw [abs_of_nonneg (norm_nonneg y), inv_mul_cancel₀ hynorm_ne]
  set A : Set (E n) := {ξ | δ ≤ 1 - inner ℝ ŷ ξ} with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact measurableSet_le measurable_const (by fun_prop)
  have hA34 : (3/4 : ℝ) ≤ (ν A).toReal := by
    rw [hA]; exact hδgap ŷ hŷSph
  set c : ℝ := Real.log (1 + δ * ((Real.exp (2 * s) - 1) / 2)) with hc
  have hK : 0 ≤ (Real.exp (2 * s) - 1) / 2 := by
    have := Real.one_le_exp (by linarith : (0:ℝ) ≤ 2 * s)
    linarith
  have hc0 : 0 ≤ c := by
    rw [hc]
    apply Real.log_nonneg
    have h1 : 0 ≤ δ * ((Real.exp (2 * s) - 1) / 2) := mul_nonneg (le_of_lt hδpos) hK
    linarith
  have hae_sph : ∀ᵐ ξ ∂ν, ξ ∈ Sph n := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  have hae : ∀ᵐ ξ ∂ν, -s + A.indicator (fun _ => c) ξ ≤ busemann ξ y := by
    filter_upwards [hae_sph] with ξ hξ
    have hrf := hRay y ξ hy_ne hξ
    rw [← hs, ← hŷ] at hrf
    by_cases hmem : ξ ∈ A
    · rw [Set.indicator_of_mem hmem, hrf.1, hc]
      have hmem' : δ ≤ 1 - inner ℝ ŷ ξ := hmem
      have h1 : 0 < 1 + δ * ((Real.exp (2 * s) - 1) / 2) := by
        have hh : 0 ≤ δ * ((Real.exp (2 * s) - 1) / 2) := mul_nonneg (le_of_lt hδpos) hK
        linarith
      have h2 : 1 + δ * ((Real.exp (2 * s) - 1) / 2)
          ≤ 1 + (1 - inner ℝ ŷ ξ) * ((Real.exp (2 * s) - 1) / 2) := by
        have hh := mul_le_mul_of_nonneg_right hmem' hK
        linarith
      have hlogineq := Real.log_le_log h1 h2
      linarith
    · rw [Set.indicator_of_notMem hmem, add_zero]
      exact hrf.2
  have hb_int : Integrable (fun ξ : E n => busemann ξ y) ν := by
    apply Integrable.mono' (MeasureTheory.integrable_const s) (measurable_busemann y).aestronglyMeasurable
    filter_upwards [hae_sph] with ξ hξ
    rw [Real.norm_eq_abs, hs]
    exact abs_busemann_le_hdist_zero ξ hξ y
  have hind_int : Integrable (fun ξ : E n => A.indicator (fun _ => c) ξ) ν := by
    apply Integrable.mono' (MeasureTheory.integrable_const |c|)
      ((measurable_const.indicator hAmeas).aestronglyMeasurable)
    filter_upwards with ξ
    rw [Real.norm_eq_abs]
    by_cases h : ξ ∈ A
    · rw [Set.indicator_of_mem h, abs_of_nonneg hc0]
    · rw [Set.indicator_of_notMem h]; simp
  have hlin_int : Integrable (fun ξ : E n => -s + A.indicator (fun _ => c) ξ) ν :=
    (MeasureTheory.integrable_const (-s)).add hind_int
  have hInt_le : ∫ ξ, (-s + A.indicator (fun _ => c) ξ) ∂ν ≤ ∫ ξ, busemann ξ y ∂ν :=
    integral_mono_ae hlin_int hb_int hae
  have hLHS : ∫ ξ, (-s + A.indicator (fun _ => c) ξ) ∂ν = -s + (ν A).toReal * c := by
    rw [integral_add (MeasureTheory.integrable_const (-s)) hind_int,
        MeasureTheory.integral_const,
        MeasureTheory.integral_indicator_const c hAmeas,
        MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
        MeasureTheory.IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul,
        smul_eq_mul]
  have hlog : Real.log (δ / 2) + 2 * s ≤ c := by
    rw [hc]
    have harg : 0 < (δ / 2) * Real.exp (2 * s) := by positivity
    have hmul : Real.log ((δ / 2) * Real.exp (2 * s)) = Real.log (δ / 2) + 2 * s := by
      rw [Real.log_mul (ne_of_gt (half_pos hδpos)) (Real.exp_ne_zero _), Real.log_exp]
    rw [← hmul]
    apply Real.log_le_log harg
    have hkey : (δ / 2) * Real.exp (2 * s) - δ * ((Real.exp (2 * s) - 1) / 2) = δ / 2 := by
      ring
    nlinarith [hδle1, hkey]
  have hlogsum : Real.log (2 / δ) + Real.log (δ / 2) = 0 := by
    rw [← Real.log_mul (div_ne_zero two_ne_zero hδne) (ne_of_gt (by positivity : (0:ℝ) < δ / 2))]
    have h1 : (2:ℝ) / δ * (δ / 2) = 1 := by field_simp
    rw [h1, Real.log_one]
  have h3 : 0 < -s + (3/4) * c := by
    nlinarith [hlog, hlogR, hlogsum]
  have h34mul : (3/4) * c ≤ (ν A).toReal * c := mul_le_mul_of_nonneg_right hA34 hc0
  have hpos_int : 0 < -s + (ν A).toReal * c := by linarith [h3, h34mul]
  have hpos : 0 < ∫ ξ, busemann ξ y ∂ν := by
    rw [hLHS] at hInt_le
    linarith [hpos_int, hInt_le]
  have hb0 : baryFun ν 0 = 0 := by simp [baryFun, busemann_zero]
  rw [hb0]
  show (0:ℝ) < ∫ ξ, busemann ξ y ∂ν
  exact hpos

end

end Work.Mostow
