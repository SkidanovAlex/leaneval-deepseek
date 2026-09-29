import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs

/-!
# Integrability of the `s₀`-slice integral over the torus cube

This file proves that the operation of integrating a function on the `(d+1)`-dimensional torus
cube over its first coordinate produces an integrable function on the `d`-dimensional torus cube.

The proof is the Fubini argument: under the measure-preserving equivalence
`ℝ × (Fin d → ℝ) ≃ᵐ (Fin (d+1) → ℝ)`, `pos p ↦ Fin.cons p.1 p.2`, the measure
`torMeasure (d+1)` is the product of `volume.restrict (Icc 0 1)` with `torMeasure d`; integrability
of `Φ` transfers to the pulled-back function, and Fubini's theorem
(`MeasureTheory.Integrable.integral_prod_right`) then gives integrability of the partial integral.
-/

namespace Work.Holonomy3

open MeasureTheory

/-- **Integrability of the `s₀`-slice integral** (general form, for an arbitrary measure `μ` on the
first coordinate). If `F` is integrable for the product measure on `Fin (d+1) → ℝ`, then the
function `s' ↦ ∫ s₀, F (Fin.cons s₀ s') ∂μ` is integrable for the product measure on
`Fin d → ℝ`. -/
theorem integrable_pi_cons_integral {d : ℕ} (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.SigmaFinite μ]
    (F : (Fin (d + 1) → ℝ) → ℝ)
    (hF : MeasureTheory.Integrable F (MeasureTheory.Measure.pi (fun _ : Fin (d + 1) => μ))) :
    MeasureTheory.Integrable
      (fun s' : Fin d → ℝ => ∫ s₀ : ℝ, F (Fin.cons s₀ s') ∂μ)
      (MeasureTheory.Measure.pi (fun _ : Fin d => μ)) := by
  -- the measure-preserving identification `ℝ × (Fin d → ℝ) ≃ᵐ (Fin (d+1) → ℝ)`
  let e : ℝ × (Fin d → ℝ) ≃ᵐ (Fin (d + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
  have he : ∀ (s : ℝ) (t' : Fin d → ℝ), e (s, t') = Fin.cons s t' := by
    intro s t'
    funext i
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hmp : MeasurePreserving e (μ.prod (Measure.pi (fun _ : Fin d => μ)))
      (Measure.pi (fun _ : Fin (d + 1) => μ)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => μ) 0).symm
  have hint : Integrable (fun p : ℝ × (Fin d → ℝ) => F (e p))
      (μ.prod (Measure.pi (fun _ : Fin d => μ))) :=
    hmp.integrable_comp_of_integrable hF
  have h2 : Integrable (fun y : Fin d → ℝ => ∫ x : ℝ, F (e (x, y)) ∂μ)
      (Measure.pi (fun _ : Fin d => μ)) := hint.integral_prod_right
  simpa only [he] using h2

theorem integrable_cons_integral {d : ℕ} (Φ : (Fin (d + 1) → ℝ) → ℝ)
    (hΦ : MeasureTheory.Integrable Φ (Work.Holonomy3.torMeasure (d + 1))) :
    MeasureTheory.Integrable
      (fun s' : Fin d → ℝ =>
        ∫ s₀ : ℝ, Φ (Fin.cons s₀ s') ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)))
      (Work.Holonomy3.torMeasure d) :=
  integrable_pi_cons_integral (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) Φ hΦ

end Work.Holonomy3
