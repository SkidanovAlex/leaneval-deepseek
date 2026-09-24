import Submission.Work.Parabolic.Deps
import Submission.Work.Parabolic.Transport
import Submission.Work.Parabolic.isOpenMap_of_injective_holomorphic
import Submission.Work.Parabolic.injFamily_nonempty_of_isOpenEmbedding_of_not_surjective
import Submission.Work.Parabolic.holomorphicOnX_comp_biholomorph
import Submission.Work.Parabolic.hasGreenFunctionAt_iUHP

/-!
# The parabolic case of uniformization: the reduction

This module assembles everything of `Work.Parabolic` into the statements that the rest of the
project consumes, with the **corrected** notion of Green function (`IsGreenFunctionAt`, relative
compactness of the superlevel sets, `Basic.lean`).

The mathematical content of the parabolic case is the following.  If `X` is a non-compact connected
Riemann surface with no Green function *and* `H¹(X,ℝ) = 0` (the challenge hypothesis
`Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)`), then `X ≅ ℂ`.  Two classical inputs are
needed, and both are made explicit hypotheses here (they are the deliverables of parallel
subprojects):

* `SimplyConnectedSpace X` — the toplogical input (`Work.Spine`,
  `Submission.simplyConnectedSpace_of_subsingleton_hom_toReal`);
* a *non-constant injective holomorphic* `φ : X → ℂ` — the ABS input (`Work.SimplyConnected`,
  every non-compact simply connected Riemann surface is biholomorphic to a domain in `ℂ`).

Given those, the argument is short: if `φ` is onto then `X ≅ ℂ`; otherwise the image `φ(X)` is a
proper simply connected plane domain, the Riemann-mapping theorem produces an injective holomorphic
function `X → 𝔻`, the extremal-function machinery of `Submission.ExtremalInj` then gives
`X ≅ ℂ` *or* `X ≅ ℍ`, and the second alternative is impossible because `ℍ` has a Green function
(`hasGreenFunctionAt_iUHP`), transported to `X` along the biholomorphism (`Transport.lean`).

The results of this module are therefore:

* `hasGreenFunction_of_biholomorphic_upperHalfPlane`,
  `isParabolic.not_nonempty_diffeomorph_upperHalfPlane` — parabolicity excludes the hyperbolic
  branch;
* `nonempty_diffeomorph_plane_of_isParabolic_of_dichotomy` — the parabolic case from the
  simply connected case (`Work.SimplyConnected`);
* `nonempty_diffeomorph_plane_of_isParabolic_of_injective_holomorphic` — the parabolic case from an
  injective holomorphic map into `ℂ`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical
open Submission

namespace Work.Parabolic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The image of a simply connected space under an open embedding is simply connected. -/
theorem isSimplyConnected_range_of_isOpenEmbedding {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace X] {φ : X → Y} (hφ : Topology.IsOpenEmbedding φ) :
    IsSimplyConnected (Set.range φ) := by
  have hsc : IsSimplyConnected (Set.univ : Set X) := by
    have h : ContinuousMap.HomotopyEquiv (Set.univ : Set X) X :=
      (Homeomorph.Set.univ X).toHomotopyEquiv
    exact h.simplyConnectedSpace
  have := (hφ.isEmbedding.isSimplyConnected_image (s := Set.univ)).mpr hsc
  simpa using this

/-! ## Parabolicity excludes the hyperbolic branch -/

/-- **`X` has a Green function as soon as it is biholomorphic to `ℍ`** (transport of the model
Green function `hasGreenFunctionAt_iUHP` along the biholomorphism). -/
theorem hasGreenFunction_of_biholomorphic_upperHalfPlane
    (Φ : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) :
    HasGreenFunction X :=
  ⟨Φ.symm iUHP, hasGreenFunctionAt_of_diffeomorph Φ hasGreenFunctionAt_iUHP⟩

/-- **A parabolic surface is not biholomorphic to `ℍ`.** -/
theorem isParabolic.not_nonempty_diffeomorph_upperHalfPlane (h : IsParabolic X) :
    ¬ Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) :=
  fun ⟨Φ⟩ => h (hasGreenFunction_of_biholomorphic_upperHalfPlane Φ)

/-- **The parabolic case from the uniformization dichotomy.**  If the dichotomy
`X ≅ ℂ ∨ X ≅ ℍ` is available (for instance from the simply connected case of the uniformization
theorem) and `X` is parabolic, then `X ≅ ℂ`. -/
theorem nonempty_diffeomorph_plane_of_isParabolic_of_dichotomy (h : IsParabolic X)
    (hdich : Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  hdich.elim id fun hH => absurd (hasGreenFunction_of_biholomorphic_upperHalfPlane hH.some) h

/-! ## The parabolic case from an injective holomorphic map into `ℂ` -/

variable [SecondCountableTopology X]

/-- **The parabolic case of the uniformization theorem, from an injective holomorphic map into
`ℂ`.**  With `SimplyConnectedSpace X` (the topological input) and a non-constant injective
holomorphic `φ : X → ℂ` (the ABS input), a parabolic `X` is biholomorphic to `ℂ`. -/
theorem nonempty_diffeomorph_plane_of_isParabolic_of_injective_holomorphic
    [SimplyConnectedSpace X] {x₀ : X} (h : IsParabolic X) {φ : X → ℂ}
    (hφ : HolomorphicOnX φ univ) (hinj : Function.Injective φ) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) := by
  by_cases hsurj : Function.Surjective φ
  · refine nonempty_diffeomorph_plane_of_bijective hφ ⟨hinj, hsurj⟩ fun x => ?_
    exact Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic hinj
      (fun y => hφ y (mem_univ y)) (exists_ne_of_chartedSpace x)
  · have hcont : Continuous φ := hφ.continuous
    have hopen : IsOpenMap φ := isOpenMap_of_injective_holomorphic hφ hinj
    have hemb : Topology.IsOpenEmbedding φ :=
      Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
    have hUc : IsSimplyConnected (Set.range φ) := isSimplyConnected_range_of_isOpenEmbedding hemb
    have hfam : (injFamily x₀).Nonempty :=
      injFamily_nonempty_of_isOpenEmbedding_of_not_surjective hφ hemb hUc hsurj
    rcases uniformization_of_injective_into_disc (x₀ := x₀) hfam with hpl | hH
    · exact hpl
    · exact absurd (hasGreenFunction_of_biholomorphic_upperHalfPlane hH.some) h

end Work.Parabolic
