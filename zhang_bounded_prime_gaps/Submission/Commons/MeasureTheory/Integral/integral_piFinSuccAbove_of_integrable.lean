import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory

theorem integral_piFinSuccAbove_of_integrable {k : ℕ} (i : Fin (k+1)) (G : (Fin (k+1) → ℝ) → ℝ) (hG : MeasureTheory.Integrable G) : ∫ y : Fin (k+1) → ℝ, G y = ∫ x : ℝ, ∫ u : Fin k → ℝ, G (Fin.insertNth i x u) := by
  let e : (Fin (k+1) → ℝ) ≃ᵐ (ℝ × (Fin k → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i
  have hmp : MeasureTheory.MeasurePreserving e volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i
  have h1 : ∫ y : Fin (k+1) → ℝ, G y = ∫ z : ℝ × (Fin k → ℝ), G (e.symm z) :=
    (hmp.symm.integral_comp' G).symm
  have h2 : ∫ z : ℝ × (Fin k → ℝ), G (e.symm z) =
      ∫ x : ℝ, ∫ u : Fin k → ℝ, G (e.symm (x, u)) :=
    MeasureTheory.integral_prod (fun z : ℝ × (Fin k → ℝ) => G (e.symm z))
      (hmp.symm.integrable_comp_of_integrable hG)
  have key : ∀ (x : ℝ) (u : Fin k → ℝ), e.symm (x, u) = Fin.insertNth i x u := by
    intro x u
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  rw [h1, h2]
  simp only [key]

end Commons.MeasureTheory.Integral