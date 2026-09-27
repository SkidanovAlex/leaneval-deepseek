import Mathlib
import Submission.Work.Drive.cutAvoidShift
import Submission.Work.Drive.exists_near_notMem_of_interior_eq_empty
import Submission.Work.Drive.blockVocabulary

/-!
# The `δc` producer of the transport `T6` from a moving block parameter

`Work.Drive.exists_deltaC_iff_notMem` (`Submission/Work/Drive/cutAvoidShift.lean`) reduces the third
conjunct of `Work.Drive.T6GenAt`

> `∃ δc > 0, ∀ x : 𝔼², ‖cplxOf x‖ ≤ δc → x ∉ diskCut Q W`

to the *single-point* avoidance `Q 0 ∉ W '' unitBox 2`, and
`Work.Drive.exists_near_notMem_of_interior_eq_empty` supplies that avoidance at parameters
arbitrarily close to any base parameter of a `ChartPert` family, as soon as the image of the chain has
empty interior.  This file assembles the two into the form the design consumes:

* `Work.Drive.exists_deltaC_shift` — the `δc` conjunct for the chart
  `z ↦ Ξ (s₀ + σ) (Q' z)` (one block's parameter moved, everything else fixed);
* the design-facing form is then a one-line instantiation at
  `Q' := rotCapping (u k) ∘ Q`, `p₀ := Q' 0`, `Ξ := chartPert`, whose image-emptiness input is supplied
  by the weak-Sard chapter (`Work.Sard.interior_image_eq_empty_of_contMDiff_of_lt`) applied to the
  clamped sweep (a `C^∞` map `𝔼³ → CappingSpace`).
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Filter Set

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **The `δc` conjunct of `T6GenAt` by a small move of one block's parameter.**  Let `Ξ` be a chart
perturbation, `Q'` a continuous plane chart and `W` a continuous chain whose image over the parameter
box has empty interior.  Then for every base parameter `s₀` and every `ε > 0` there are parameters
`σ` of norm `< ε` such that the perturbed chart `z ↦ Ξ (s₀ + σ) (Q' z)` satisfies the cut avoidance
`∃ δc > 0, ∀ x, ‖cplxOf x‖ ≤ δc → x ∉ diskCut (Ξ (s₀+σ) ∘ Q') W`. -/
theorem exists_deltaC_shift {Q' : ℂ → CappingSpace} (hQ' : Continuous Q')
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace} (hΞ : ChartPert Q' 4 Ξ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) (hW : Continuous W)
    (hWint : interior (W '' Submission.Drive.unitBox 2) = ∅)
    (s₀ : EuclideanSpace ℝ (Fin 4)) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : EuclideanSpace ℝ (Fin 4), ‖σ‖ < ε ∧
      ∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
        x ∉ diskCut (fun z : ℂ => Ξ (s₀ + σ) (Q' z)) W := by
  obtain ⟨σ, hσ, hmem⟩ :=
    exists_near_notMem_of_interior_eq_empty hΞ (Q' 0) (W '' Submission.Drive.unitBox 2) hWint s₀ ε hε
  refine ⟨σ, hσ, ?_⟩
  have hcont : Continuous (fun z : ℂ => Ξ (s₀ + σ) (Q' z)) :=
    (contMDiff_apply_of_chartPert hΞ (s₀ + σ)).continuous.comp hQ'
  exact (exists_deltaC_iff_notMem (fun z : ℂ => Ξ (s₀ + σ) (Q' z)) W hcont hW).mpr hmem

end Work.Drive
