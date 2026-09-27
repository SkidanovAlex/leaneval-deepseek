import Submission.UnifDeps
import Submission.Holomorphic
import Submission.Commons.Analysis.Complex.bijective_of_isProperMap_holomorphic_single_zero

/-!
# The endgame: a proper holomorphic map with a single simple zero is bijective

`Commons.Analysis.Complex.bijective_of_isProperMap_holomorphic_single_zero` (proved by the fleet)
states that a proper holomorphic map `Φ : X → ℂ` on a connected, second countable complex
one-manifold with `Φ ⁻¹' {0} = {z₀}` and non-vanishing derivative at `z₀` is **bijective**.  This
is the classical "degree one" argument: the fibre of a regular value is locally constant, the
regular values are connected, and a critical point would force some regular value to have at least
two preimages.

This module restates it in the vocabulary of `Submission` (`HolomorphicOnX`), so that it applies
directly to the maps produced by the Green-function and extremal constructions.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A proper holomorphic map with a single simple zero is bijective.** -/
theorem bijective_of_proper_single_zero {Φ : X → ℂ} (hΦ : HolomorphicOnX Φ univ)
    (hprop : IsProperMap Φ) {z₀ : X} (hfib : Φ ⁻¹' {0} = {z₀})
    (hloc : deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0) :
    Function.Bijective Φ :=
  Commons.Analysis.Complex.bijective_of_isProperMap_holomorphic_single_zero
    (fun x => hΦ x (mem_univ x)) hprop hfib hloc

/-- Version with the fibre hypothesis in pointwise form. -/
theorem bijective_of_proper_single_zero' {Φ : X → ℂ} (hΦ : HolomorphicOnX Φ univ)
    (hprop : IsProperMap Φ) {z₀ : X} (hfib : ∀ x : X, Φ x = 0 ↔ x = z₀)
    (hloc : deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0) :
    Function.Bijective Φ := by
  refine bijective_of_proper_single_zero hΦ hprop ?_ hloc
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  exact hfib x

end Submission
