import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped ENNReal

namespace Commons.MeasureTheory

/-- Multiplying a measure on `ℝ` by a nonzero constant `c : ℝ≥0∞` does not change the
almost-everywhere filter: `(c • μ).ae = μ.ae`. -/
lemma eventually_smul_measure_eq {c : ℝ≥0∞} (hc : c ≠ 0) {μ : Measure ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ x ∂(c • μ), P x) : ∀ᵐ x ∂μ, P x :=
  h.filter_mono (Measure.AbsolutelyContinuous.ae_le (Measure.absolutelyContinuous_smul hc))

/-- Affine change of variables for the Lebesgue measure restricted to a left-open interval:
an almost-everywhere statement on `(0, T]` transfers, via `s ↦ t₀ + lam * s`, to an
almost-everywhere statement on `(t₀, t₀ + lam * T]` under the inverse substitution
`t ↦ (t - t₀) / lam`. -/
theorem ae_restrict_Ioc_add_mul {t₀ lam T : ℝ} (hlam : 0 < lam) {P : ℝ → Prop}
    (h : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T)), P s) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc t₀ (t₀ + lam * T))), P ((t - t₀) / lam) := by
  have hf : MeasurableEmbedding (fun s : ℝ => t₀ + lam * s) :=
    (Homeomorph.addLeft t₀).measurableEmbedding.comp
      (Homeomorph.mulLeft₀ lam hlam.ne').measurableEmbedding
  have hpre : (fun s : ℝ => t₀ + lam * s) ⁻¹' Set.Ioc t₀ (t₀ + lam * T) = Set.Ioc (0:ℝ) T := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
  have h1 : Measure.map (fun s : ℝ => t₀ + lam * s) volume
      = ENNReal.ofReal lam⁻¹ • (volume : Measure ℝ) := by
    have hcomp : (fun s : ℝ => t₀ + lam * s)
        = (fun u : ℝ => t₀ + u) ∘ (fun s : ℝ => lam * s) := rfl
    rw [hcomp, ← Measure.map_map (measurable_const_add t₀) (measurable_const_mul lam),
      Real.map_volume_mul_left hlam.ne', Measure.map_smul,
      MeasureTheory.map_add_left_eq_self volume t₀, abs_of_pos (inv_pos.mpr hlam)]
  have hmap : Measure.map (fun s : ℝ => t₀ + lam * s) (volume.restrict (Set.Ioc (0:ℝ) T))
      = ENNReal.ofReal lam⁻¹ • (volume.restrict (Set.Ioc t₀ (t₀ + lam * T))) := by
    rw [← hpre, ← Measure.restrict_map hf.measurable measurableSet_Ioc, h1, Measure.restrict_smul]
  have h2 : ∀ᵐ t ∂(Measure.map (fun s : ℝ => t₀ + lam * s) (volume.restrict (Set.Ioc (0:ℝ) T))),
      P ((t - t₀) / lam) := by
    refine (hf.ae_map_iff).mpr ?_
    filter_upwards [h] with s hs
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hlam.ne']
    exact hs
  rw [hmap] at h2
  have hc : (ENNReal.ofReal lam⁻¹) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (inv_pos.mpr hlam)
  exact eventually_smul_measure_eq hc h2

end Commons.MeasureTheory