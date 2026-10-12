import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Fubini in the coordinates of `Fin n → ℝ`

The `lintegral` against the Lebesgue measure on `Fin n → ℝ` (which is the product measure
`Measure.pi (fun _ => volume)`) expressed as an iterated `lintegral` in the coordinates.
This is the standard Tonelli/Fubini identity for the product measure, obtained from
`MeasurableEquiv.piFinSuccAbove` + `MeasureTheory.volume_preserving_piFinSuccAbove` +
`MeasurePreserving.lintegral_comp` + `MeasureTheory.lintegral_prod`.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1S

/-- **Peel one coordinate** of an integral over `Fin (n+1) → ℝ`. -/
theorem lintegralPi_peel_one {n : ℕ} (G : (Fin (n+1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y : Fin (n+1) → ℝ, G y = ∫⁻ y₀ : ℝ, ∫⁻ y₁ : Fin n → ℝ, G (Fin.cons y₀ y₁) := by
  set e : (Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (0 : Fin (n+1)) with he
  have hmp : MeasurePreserving e.symm (volume : Measure (ℝ × (Fin n → ℝ))) volume :=
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (0 : Fin (n+1))).symm
  have hmeas : Measurable (fun p : ℝ × (Fin n → ℝ) => G (e.symm p)) :=
    hG.comp (MeasurableEquiv.measurable e.symm)
  have h1 : ∫⁻ p : ℝ × (Fin n → ℝ), G (e.symm p) = ∫⁻ y : Fin (n+1) → ℝ, G y :=
    hmp.lintegral_comp hG
  rw [← h1]
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = volume.prod volume from rfl]
  rw [MeasureTheory.lintegral_prod _ hmeas.aemeasurable]
  congr 1 with y₀
  congr 1 with y₁
  simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero', Equiv.coe_fn_mk]

/-- **The `Fin 1 → ℝ` integral is the integral over `ℝ`.** -/
theorem lintegral_fin1 (H : (Fin 1 → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ y : Fin 1 → ℝ, H y = ∫⁻ a : ℝ, H ![a] := by
  set e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ with he
  have hmp : MeasurePreserving e.symm (volume : Measure ℝ) volume :=
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  have h1 : ∫⁻ a : ℝ, H (e.symm a) = ∫⁻ y : Fin 1 → ℝ, H y := hmp.lintegral_comp hH
  rw [← h1]
  refine lintegral_congr fun a => ?_
  have h2 : e.symm a = ![a] := by
    refine e.injective ?_
    rw [e.apply_symm_apply]
    rw [he]
    simp [MeasurableEquiv.funUnique_apply]
  rw [h2]

/-- **Peel the coordinates of `ℝ²`.** -/
theorem lintegralPi2_peel (G : (Fin 2 → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y, G y = ∫⁻ y₀ : ℝ, ∫⁻ y₁ : ℝ, G ![y₀, y₁] := by
  rw [lintegralPi_peel_one (n := 1) G hG]
  refine lintegral_congr fun y₀ => ?_
  have hc_meas : Measurable (fun y₁ : Fin 1 → ℝ => (@Fin.cons 1 (fun _ : Fin 2 => ℝ) y₀ y₁)) := by
    have hc : (fun y₁ : Fin 1 → ℝ => (@Fin.cons 1 (fun _ : Fin 2 => ℝ) y₀ y₁))
        = fun y₁ => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) (0 : Fin 2)).symm
            (y₀, y₁) := by
      funext y₁
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero', Equiv.coe_fn_mk]
    rw [hc]
    exact (MeasurableEquiv.measurable _).comp (by fun_prop)
  rw [lintegral_fin1 (fun y₁ : Fin 1 → ℝ => G (@Fin.cons 1 (fun _ : Fin 2 => ℝ) y₀ y₁))
    (hG.comp hc_meas)]
  refine lintegral_congr fun a => ?_
  congr 1

/-- **Peel the coordinates of `ℝ³`.** -/
theorem lintegralPi3_peel (G : (Fin 3 → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y, G y = ∫⁻ y₀ : ℝ, ∫⁻ y₁ : ℝ, ∫⁻ y₂ : ℝ, G ![y₀, y₁, y₂] := by
  rw [lintegralPi_peel_one (n := 2) G hG]
  refine lintegral_congr fun y₀ => ?_
  have hc_meas : Measurable (fun y' : Fin 2 → ℝ => (@Fin.cons 2 (fun _ : Fin 3 => ℝ) y₀ y')) := by
    have hc : (fun y' : Fin 2 → ℝ => (@Fin.cons 2 (fun _ : Fin 3 => ℝ) y₀ y'))
        = fun y' => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (0 : Fin 3)).symm
            (y₀, y') := by
      funext y'
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero', Equiv.coe_fn_mk]
    rw [hc]
    exact (MeasurableEquiv.measurable _).comp (by fun_prop)
  rw [lintegralPi2_peel (fun y' : Fin 2 → ℝ => G (@Fin.cons 2 (fun _ : Fin 3 => ℝ) y₀ y'))
    (hG.comp hc_meas)]
  refine lintegral_congr fun a => ?_
  refine lintegral_congr fun b => ?_
  congr 1


end Work.BoseFixB1S
