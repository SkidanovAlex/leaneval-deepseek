import Mathlib
import Submission.Work.WilE9G.Sard.FlatDefs

/-!
# The equal-dimensional base case of the analytic Sard theorem

If `F : ℝᵈ → ℝᵈ` is real analytic on an open set `W`, then the image of the critical set
`{x | fderiv ℝ F x is not surjective}` (intersected with `W`) is Lebesgue-null.

This is the fixed-dimension Sard lemma of Mathlib
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`): for a square map the
non-surjectivity of the Fréchet derivative at `x` is equivalent to the vanishing of its
determinant, and the image of a set on which the derivative is everywhere singular is null.

`W` is open only to make sure that on the relevant set the function is differentiable in the
honest sense (so that `HasFDerivWithinAt` holds there); nothing else uses the openness of `W`.
-/

set_option autoImplicit false

namespace Work.WilE9G.Sard

open MeasureTheory

/-- On the critical set of a square map the Jacobian determinant vanishes. -/
lemma det_fderiv_eq_zero_of_mem_critSet {d : ℕ} {F : (Fin d → ℝ) → (Fin d → ℝ)}
    {x : Fin d → ℝ} (h : x ∈ critSet F) : (fderiv ℝ F x).det = 0 :=
  det_eq_zero_of_not_surjective (fderiv ℝ F x) (mem_critSet.mp h)

theorem baseCaseEq {d : ℕ} (F : (Fin d → ℝ) → (Fin d → ℝ)) (W : Set (Fin d → ℝ))
    (hW : IsOpen W) (hF : AnalyticOn ℝ F W) (A : Set (Fin d → ℝ)) (hA : A ⊆ W)
    (hcrit : A ⊆ critSet F) : MeasureTheory.volume (F '' A) = 0 := by
  have hsub : A ⊆ W ∩ critSet F := fun x hx => ⟨hA hx, hcrit hx⟩
  refine measure_mono_null (Set.image_mono hsub) ?_
  refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (μ := MeasureTheory.volume) (f := F) (s := W ∩ critSet F)
    (f' := fun x => fderiv ℝ F x) ?_ ?_
  · intro x hx
    have hxan : AnalyticAt ℝ F x := hF.analyticAt (hW.mem_nhds hx.1)
    exact hxan.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact det_fderiv_eq_zero_of_mem_critSet hx.2

end Work.WilE9G.Sard
