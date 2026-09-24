import ChallengeDeps
import Submission.Work.SimplyConnected.Basic
import Submission.PlanarUniformization
import Submission.Packaging
import Submission.Work.Parabolic.isOpenMap_of_injective_holomorphic
import Submission.Work.SimplyConnected.Parabolic.isSimplyConnected_range_of_injective_holomorphic

/-!
# The simply connected case of uniformization, reduced to an injective map into `ℂ`

This module contains the **wiring** of the deliverable of `Submission/Work/SimplyConnected/` to the
single classical input of the chapter (the "ABS input", Anghel–Bruin–Stan / Hubbard Theorem 1.1.1,
[ABS, Theorem 1]): *a non-compact simply connected Riemann surface admits an injective holomorphic
map into `ℂ`* (equivalently: it is biholomorphic to a domain in `ℂ`).

```
Work.SC.uniformization_of_simplyConnected_of_injective_into_plane
    [SimplyConnectedSpace X] (hX : ¬ CompactSpace X)
    {φ : X → ℂ} (hφ : Submission.HolomorphicOnX φ Set.univ) (hinj : Function.Injective φ) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane)
```

The proof is a two-case analysis on the image of `φ`:

* if `φ` is onto `ℂ`, then `Submission.nonempty_diffeomorph_plane_of_bijective` exhibits a complex
  diffeomorphism `X ≃ₘ ℂ` (the chart derivative is non-zero by injectivity,
  `Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic`);
* otherwise `U := Set.range φ` is an *open, simply connected, proper* planar domain and
  `Submission.uniformization_of_injective_to_simplyConnected` (which invokes the first half of the
  Riemann mapping theorem, `Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero`)
  gives the conclusion — indeed `X ≅ 𝔻`.

The two facts about the image of an injective holomorphic map that are used here are
`Work.Parabolic.isOpenMap_of_injective_holomorphic` (the open mapping theorem) and
`Work.SimplyConnected.Parabolic.isSimplyConnected_range_of_injective_holomorphic` (the image of a
simply connected space under an injective holomorphic map is simply connected).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SC

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The simply connected case of uniformization from an injective holomorphic map into `ℂ`.**

If a simply connected, non-compact Riemann surface `X` admits an injective holomorphic map into
`ℂ` — the classical "ABS input", *every non-compact simply connected Riemann surface is
biholomorphic to a domain in `ℂ`* — then `X` is biholomorphic to `ℂ` or to the upper half plane. -/
theorem uniformization_of_simplyConnected_of_injective_into_plane [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) {φ : X → ℂ} (hφ : Submission.HolomorphicOnX φ Set.univ)
    (hinj : Function.Injective φ) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
  by_cases hsurj : Function.Surjective φ
  · -- `φ` is a biholomorphism onto `ℂ`
    have hderiv : ∀ x : X, deriv (φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := fun x =>
      Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic (X := X) (Φ := φ) hinj
        (fun y => hφ y (mem_univ y)) (Submission.exists_ne_of_chartedSpace x)
    exact Or.inl (Submission.nonempty_diffeomorph_plane_of_bijective hφ ⟨hinj, hsurj⟩ hderiv)
  · -- the image is a proper simply connected planar domain
    have hI : Nonempty X := inferInstance
    obtain ⟨x₀⟩ := hI
    haveI : Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ) :=
      subsingleton_hom_additive_fundamentalGroup_of_simplyConnected x₀
    have hopen : IsOpenMap φ := Work.Parabolic.isOpenMap_of_injective_holomorphic hφ hinj
    have hUo : IsOpen (Set.range φ) := hopen.isOpen_range
    have hUc : IsSimplyConnected (Set.range φ) :=
      Work.SimplyConnected.Parabolic.isSimplyConnected_range_of_injective_holomorphic hφ hinj
    have hUne : Set.range φ ≠ Set.univ := by
      intro h
      exact hsurj fun y => by
        have : y ∈ Set.range φ := by rw [h]; exact Set.mem_univ y
        exact this
    exact Submission.uniformization_of_injective_to_simplyConnected (x₀ := x₀) hφ hinj hUo hUc
      hUne (Set.Subset.refl _)

end Work.SC

namespace Work.SimplyConnected

/-- Alias of `Work.SC.uniformization_of_simplyConnected_of_injective_into_plane`. -/
alias uniformization_of_simplyConnected_of_injective_into_plane :=
  Work.SC.uniformization_of_simplyConnected_of_injective_into_plane

end Work.SimplyConnected
