/-
# Level-set mass extraction against a bounded weight

Let `0 ≤ f` be an integrable "mass density" on `(0,1]` and let `w` be a (not necessarily
measurable) weight with `0 ≤ w ≤ K0`.  If the weighted mass is large, `μ ≤ ∫ f w²`, while the
plain mass is bounded, `∫ f ≤ Gf`, then some level `ε > 0` has a level set `{ε ≤ w}` which still
carries a definite fraction of the mass,

`μ/(2 K0²) ≤ ∫ {ε ≤ w} f`,

and `ε` may be taken as large as `1 / max 2 √(2 Gf/μ)` (which is what the third conjunct below
records, in the form `ε^{-Kw} ≤ (max 2 √(2 Gf/μ))^{Kw}` for `Kw > 0`).

The proof is the elementary layer-cake inequality `f w² ≤ K0² · 1_{ε ≤ w} f + ε² f`, integrated.
The one technical point is that `w` need not be measurable: the level-set truncation
`x ↦ if ε ≤ w x then f x else 0` is *not* obviously measurable.  This is handled by replacing `w`
by the measurable surrogate `W x = √(f x · w x² / f x)`, which agrees with `w` wherever `f x ≠ 0`
(and the truncation is `0` anyway where `f x = 0`).
-/
import Mathlib

set_option linter.unusedVariables false

open MeasureTheory
open Filter

namespace Work.KMTAreas.A4

namespace LevelSetMassAux

/-- The elementary pointwise level-set inequality: for `0 ≤ f` and `0 ≤ u ≤ K`,
`f u² ≤ K² · (if ε ≤ u then f else 0) + ε² f`.  (No hypothesis on the sign of `ε` is needed:
in the case `¬ ε ≤ u` one has `0 ≤ u < ε`.) -/
theorem levelSetPointwiseLe' {f u K ε : ℝ} (hf : 0 ≤ f) (hu0 : 0 ≤ u) (huK : u ≤ K) :
    f * u ^ 2 ≤ K ^ 2 * (if ε ≤ u then f else 0) + ε ^ 2 * f := by
  by_cases h : ε ≤ u
  · rw [if_pos h]
    have h1 : u ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hu0 huK 2
    have h2 : f * u ^ 2 ≤ f * K ^ 2 := mul_le_mul_of_nonneg_left h1 hf
    have h3 : 0 ≤ ε ^ 2 * f := mul_nonneg (sq_nonneg ε) hf
    nlinarith [h2, h3]
  · rw [if_neg h]
    have h1 : u ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hu0 (le_of_lt (not_le.mp h)) 2
    have h2 : f * u ^ 2 ≤ f * ε ^ 2 := mul_le_mul_of_nonneg_left h1 hf
    nlinarith [h2]

/-- **Level-set extraction** (general form).  On an arbitrary measure space, for `0 ≤ f`,
`0 ≤ u ≤ K0` with `u` a.e. measurable, `f` and `f u²` integrable, `μ ≤ ∫ f u²` and
`∫ f ≤ Gf`, any `ε` with `ε² Gf ≤ μ/2` satisfies
`μ/(2 K0²) ≤ ∫ {ε ≤ u} f`. -/
theorem levelSetAux {α : Type*} [MeasurableSpace α] (ν : Measure α) (f u : α → ℝ)
    {K0 μ Gf ε : ℝ} (hK0 : 0 < K0) (hfi : Integrable f ν)
    (hfu : Integrable (fun a => f a * u a ^ 2) ν)
    (hf0 : ∀ a, 0 ≤ f a) (hu0 : ∀ a, 0 ≤ u a) (huK : ∀ a, u a ≤ K0)
    (hum : AEMeasurable u ν)
    (hμle : μ ≤ ∫ a, f a * u a ^ 2 ∂ν) (hfG : ∫ a, f a ∂ν ≤ Gf)
    (hεG : ε ^ 2 * Gf ≤ μ / 2) :
    μ / (2 * K0 ^ 2) ≤ ∫ a, (if ε ≤ u a then f a else 0) ∂ν := by
  have hfm : AEMeasurable f ν := hfi.aemeasurable
  have hInd_meas : AEMeasurable (fun a => if ε ≤ u a then f a else 0) ν := by
    have h1 : AEMeasurable ((fun x : ℝ => if ε ≤ x then (1 : ℝ) else 0) ∘ u) ν :=
      (Measurable.ite measurableSet_Ici measurable_const measurable_const).comp_aemeasurable hum
    have h2 : AEMeasurable (fun a => ((fun x : ℝ => if ε ≤ x then (1 : ℝ) else 0) ∘ u) a * f a) ν :=
      h1.mul hfm
    refine h2.congr (Eventually.of_forall fun a => ?_)
    change (if ε ≤ u a then (1 : ℝ) else 0) * f a = (if ε ≤ u a then f a else 0)
    by_cases h : ε ≤ u a <;> simp [h]
  have hInd_int : Integrable (fun a => if ε ≤ u a then f a else 0) ν := by
    refine hfi.mono' hInd_meas.aestronglyMeasurable ?_
    filter_upwards with a
    by_cases h : ε ≤ u a
    · simp [h, Real.norm_of_nonneg (hf0 a)]
    · rw [if_neg h, norm_zero]; exact hf0 a
  have hpt : ∀ a, f a * u a ^ 2 ≤ K0 ^ 2 * (if ε ≤ u a then f a else 0) + ε ^ 2 * f a :=
    fun a => levelSetPointwiseLe' (hf0 a) (hu0 a) (huK a)
  have hbig : Integrable (fun a => K0 ^ 2 * (if ε ≤ u a then f a else 0) + ε ^ 2 * f a) ν :=
    (hInd_int.const_mul _).add (hfi.const_mul _)
  have hineq : μ ≤ K0 ^ 2 * (∫ a, (if ε ≤ u a then f a else 0) ∂ν) + μ / 2 := by
    have h1 : μ ≤ ∫ a, K0 ^ 2 * (if ε ≤ u a then f a else 0) + ε ^ 2 * f a ∂ν :=
      le_trans hμle (integral_mono_ae hfu hbig (Eventually.of_forall hpt))
    rw [integral_add (hInd_int.const_mul _) (hfi.const_mul _), integral_const_mul,
      integral_const_mul] at h1
    have h2 : ε ^ 2 * (∫ a, f a ∂ν) ≤ μ / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hfG (sq_nonneg ε)) hεG
    linarith
  have hkey : μ / 2 ≤ K0 ^ 2 * (∫ a, (if ε ≤ u a then f a else 0) ∂ν) := by linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K0 ^ 2)]
  nlinarith [hkey]

end LevelSetMassAux

open LevelSetMassAux

/-- **Level-set mass extraction.**  See the module docstring. -/
theorem levelSetMass (f w : ℝ → ℝ) {K0 μ Gf Kw : ℝ} (hK0 : 0 < K0) (hGf : 0 < Gf)
    (hμ : 0 < μ) (hKw : 0 < Kw) (hf0 : ∀ t : ℝ, 0 ≤ f t) (hw0 : ∀ t : ℝ, 0 ≤ w t)
    (hwK : ∀ t : ℝ, w t ≤ K0)
    (hfi : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hfwi : MeasureTheory.Integrable (fun t : ℝ => f t * w t ^ 2) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hfG : ∫ t in (0 : ℝ)..1, f t ≤ Gf)
    (hμle : μ ≤ ∫ t in (0 : ℝ)..1, f t * w t ^ 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε ^ (-Kw) ≤ (max 2 (Real.sqrt (2 * Gf / μ))) ^ Kw ∧
      ε ^ 2 * Gf ≤ μ / 2 ∧
      μ / (2 * K0 ^ 2) ≤ ∫ t in (0 : ℝ)..1, (if ε ≤ w t then f t else 0) := by
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hμle hfG
  set M : ℝ := max 2 (Real.sqrt (2 * Gf / μ)) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    exact lt_of_lt_of_le (by norm_num) (le_max_left 2 _)
  set W : ℝ → ℝ := fun t => Real.sqrt (f t * w t ^ 2 / f t) with hWdef
  have hW_eq : ∀ t : ℝ, f t ≠ 0 → W t = w t := by
    intro t ht
    simp only [hWdef]
    rw [mul_div_cancel_left₀ (w t ^ 2) ht, Real.sqrt_sq_eq_abs, abs_of_nonneg (hw0 t)]
  have hW0 : ∀ t : ℝ, 0 ≤ W t := fun t => by
    simp only [hWdef]
    exact Real.sqrt_nonneg _
  have hWK : ∀ t : ℝ, W t ≤ K0 := by
    intro t
    by_cases ht : f t = 0
    · have h1 : W t = 0 := by
        simp only [hWdef]
        rw [ht]
        simp
      rw [h1]
      exact hK0.le
    · rw [hW_eq t ht]
      exact hwK t
  have hWm : AEMeasurable W (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    simp only [hWdef]
    exact (hfwi.aemeasurable.div hfi.aemeasurable).sqrt
  have hWInt : Integrable (fun t => f t * W t ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine hfwi.congr (Eventually.of_forall fun t => ?_)
    show f t * w t ^ 2 = f t * W t ^ 2
    by_cases ht : f t = 0
    · simp [ht]
    · rw [hW_eq t ht]
  have hμleW : μ ≤ ∫ t, f t * W t ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [show (∫ t, f t * W t ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = (∫ t, f t * w t ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))) from
      integral_congr_ae (Eventually.of_forall fun t => by
        show f t * W t ^ 2 = f t * w t ^ 2
        by_cases ht : f t = 0
        · simp [ht]
        · rw [hW_eq t ht])]
    exact hμle
  have hsqM : 2 * Gf / μ ≤ M ^ 2 := by
    have h1 : Real.sqrt (2 * Gf / μ) ≤ M := by
      rw [hMdef]; exact le_max_right 2 _
    have h2 : (Real.sqrt (2 * Gf / μ)) ^ 2 = 2 * Gf / μ := Real.sq_sqrt (by positivity)
    calc 2 * Gf / μ = (Real.sqrt (2 * Gf / μ)) ^ 2 := h2.symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hε2 : (M⁻¹) ^ 2 * Gf ≤ μ / 2 := by
    have hkey : Gf * 2 ≤ μ * M ^ 2 := by
      have h := (div_le_iff₀ hμ).mp hsqM
      nlinarith [h]
    rw [inv_pow, ← div_eq_inv_mul]
    exact (div_le_div_iff₀ (pow_pos hMpos 2) (by norm_num : (0 : ℝ) < 2)).mpr hkey
  refine ⟨M⁻¹, inv_pos.mpr hMpos, ?_, ?_, hε2, ?_⟩
  · have h2M : 2 ≤ M := by rw [hMdef]; exact le_max_left 2 _
    simpa [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) h2M
  · have h : M⁻¹ ^ (-Kw) = M ^ Kw := by
      rw [Real.inv_rpow hMpos.le, Real.rpow_neg hMpos.le, inv_inv]
    exact le_of_eq h
  · rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [show (∫ t, (if M⁻¹ ≤ w t then f t else 0) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = (∫ t, (if M⁻¹ ≤ W t then f t else 0) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))) from
      integral_congr_ae (Eventually.of_forall fun t => by
        show (if M⁻¹ ≤ w t then f t else 0) = (if M⁻¹ ≤ W t then f t else 0)
        by_cases ht : f t = 0
        · simp [ht]
        · rw [hW_eq t ht])]
    exact levelSetAux (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) f W hK0 hfi hWInt
      hf0 hW0 hWK hWm hμleW hfG hε2

end Work.KMTAreas.A4
