import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.Packaging
import Submission.Lib.Unif2.PackagingOpen
import Submission.Lib.Unif2.Endgame
import Submission.Lib.Unif2.Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
import Submission.Lib.Unif2.Commons.Analysis.Complex.bijective_of_properInto_ball_holomorphic_single_zero

/-!
# The endgame interface for the uniformization theorem

The two routes to the uniformization theorem (the Green function and the extremal function) both
produce, in the *parabolic* case, a proper holomorphic map `Φ : X → ℂ` with `Φ ⁻¹' {0} = {z₀}` and
a simple zero at `z₀`, and, in the *hyperbolic* case, a proper holomorphic map `Φ : X → 𝔻` with the
same property.

This module records the consequences of such a map, so that a future construction only has to
produce it:

* `Submission.nonempty_diffeomorph_plane_of_proper_single_zero` — such a `Φ` into `ℂ` is a complex
  diffeomorphism onto `ℂ` (combining the degree-one lemma
  `Submission.bijective_of_proper_single_zero` with the non-vanishing derivative
  `Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic` and the packaging
  `Submission.nonempty_diffeomorph_plane_of_bijective`);

* `Submission.uniformization_of_proper_single_zero` — the first disjunct of the conclusion.
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

/-- `X` has at least two points (it is non-compact). -/
theorem exists_ne_of_not_compactSpace (hX : ¬ CompactSpace X) (z : X) : ∃ y : X, y ≠ z := by
  by_contra h
  simp only [not_exists, not_not] at h
  refine hX ?_
  have : Subsingleton X := ⟨fun a b => by rw [h a, h b]⟩
  infer_instance

/-- **A proper holomorphic map `X → ℂ` with a single simple zero is a complex diffeomorphism onto
`ℂ`.** -/
theorem nonempty_diffeomorph_plane_of_proper_single_zero (hX : ¬ CompactSpace X) {Φ : X → ℂ}
    (hΦ : HolomorphicOnX Φ univ) (hprop : IsProperMap Φ) {z₀ : X} (hfib : Φ ⁻¹' {0} = {z₀})
    (hloc : deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) := by
  have hbij : Function.Bijective Φ :=
    bijective_of_proper_single_zero hΦ hprop hfib hloc
  refine nonempty_diffeomorph_plane_of_bijective hΦ hbij fun z => ?_
  exact Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic hbij.1
    (fun x => hΦ x (mem_univ x)) (exists_ne_of_not_compactSpace hX z)

/-- **The uniformization theorem, from a proper holomorphic map onto `ℂ` with a single simple
zero.** -/
theorem uniformization_of_proper_single_zero (hX : ¬ CompactSpace X) {Φ : X → ℂ}
    (hΦ : HolomorphicOnX Φ univ) (hprop : IsProperMap Φ) {z₀ : X} (hfib : Φ ⁻¹' {0} = {z₀})
    (hloc : deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Or.inl (nonempty_diffeomorph_plane_of_proper_single_zero hX hΦ hprop hfib hloc)

/-- **The uniformization theorem, from a proper holomorphic map into the unit disc with a single
simple zero.**  The map is a biholomorphism onto `𝔻` (commons
`bijective_of_properInto_ball_holomorphic_single_zero`), whence the second disjunct of the
conclusion via `Submission.uniformization_of_bijective_to_disc`. -/
theorem uniformization_of_proper_single_zero_disc (hX : ¬ CompactSpace X) {Φ : X → ℂ}
    (hmaps : ∀ x : X, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hprop : ∀ K : Set ℂ, IsCompact K → IsCompact (Φ ⁻¹' (K ∩ Metric.ball (0 : ℂ) 1)))
    (hΦ : HolomorphicOnX Φ univ) {z₀ : X} (hfib : Φ ⁻¹' {0} = {z₀})
    (hloc : deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  have hbij := Commons.Analysis.Complex.bijective_of_properInto_ball_holomorphic_single_zero
    hmaps hprop (fun x => hΦ x (mem_univ x)) hfib hloc
  have hderiv : ∀ z : X, deriv (Φ ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) ≠ 0 := fun z =>
    Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
      (fun a b hab => hbij.1 (Subtype.ext hab))
      (fun x => hΦ x (mem_univ x)) (exists_ne_of_not_compactSpace hX z)
  exact uniformization_of_bijective_to_disc hmaps hbij hΦ hderiv

end Submission
