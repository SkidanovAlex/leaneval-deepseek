import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.pi_integral_cons

namespace Work.Holonomy3

open MeasureTheory

/-- `pi_integral_cons` with the iterated integral on the right written with the *tail*
coordinate as the outer integral: this is the Fubini-swapped form of
`Work.Holonomy3.pi_integral_cons`, obtained by combining the product decomposition of
`Measure.pi` with `integral_prod_symm`. -/
theorem pi_integral_cons_tail {d : ℕ} (ν : MeasureTheory.Measure ℝ) [MeasureTheory.SigmaFinite ν]
    (F : (Fin (d+1) → ℝ) → ℝ)
    (hF : MeasureTheory.Integrable F (MeasureTheory.Measure.pi (fun _ : Fin (d+1) => ν))) :
    ∫ t, F t ∂(MeasureTheory.Measure.pi (fun _ : Fin (d+1) => ν))
      = ∫ s' : Fin d → ℝ,
          (∫ s₀ : ℝ, F (Fin.cons s₀ s') ∂ν)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin d => ν)) := by
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
  rw [← hmp.integral_comp' F,
    integral_prod_symm (fun p : ℝ × (Fin d → ℝ) => F (e p)) hint]
  simp_rw [he]

theorem torMeasure_cons_integral {d : ℕ} (Φ : (Fin (d + 1) → ℝ) → ℝ)
    (hΦ : MeasureTheory.Integrable Φ (Work.Holonomy3.torMeasure (d + 1))) :
    ∫ t, Φ t ∂(Work.Holonomy3.torMeasure (d + 1))
      = ∫ s' : Fin d → ℝ,
          (∫ s₀ : ℝ, Φ (Fin.cons s₀ s') ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)))
        ∂(Work.Holonomy3.torMeasure d) := by
  exact pi_integral_cons_tail (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) Φ hΦ

end Work.Holonomy3
