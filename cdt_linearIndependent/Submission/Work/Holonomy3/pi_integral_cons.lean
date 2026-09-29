import Mathlib

namespace Work.Holonomy3

open MeasureTheory

theorem pi_integral_cons {d : ℕ} (ν : MeasureTheory.Measure ℝ) [MeasureTheory.SigmaFinite ν]
    (F : (Fin (d+1) → ℝ) → ℝ)
    (hF : MeasureTheory.Integrable F (MeasureTheory.Measure.pi (fun _ : Fin (d+1) => ν))) :
    ∫ t, F t ∂(MeasureTheory.Measure.pi (fun _ : Fin (d+1) => ν))
      = ∫ s, (∫ t' : Fin d → ℝ, F (Fin.cons s t') ∂(MeasureTheory.Measure.pi (fun _ : Fin d => ν))) ∂ν := by
  let e : ℝ × (Fin d → ℝ) ≃ᵐ (Fin (d+1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  have he : ∀ (s : ℝ) (t' : Fin d → ℝ), e (s, t') = Fin.cons s t' := by
    intro s t'
    funext i
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hmp : MeasurePreserving e (ν.prod (Measure.pi (fun _ : Fin d => ν)))
      (Measure.pi (fun _ : Fin (d+1) => ν)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => ν) 0).symm
  have hint : Integrable (fun p : ℝ × (Fin d → ℝ) => F (e p))
      (ν.prod (Measure.pi (fun _ : Fin d => ν))) :=
    hmp.integrable_comp_of_integrable hF
  rw [← hmp.integral_comp' F, integral_prod (fun p : ℝ × (Fin d → ℝ) => F (e p)) hint]
  simp_rw [he]

end Work.Holonomy3
