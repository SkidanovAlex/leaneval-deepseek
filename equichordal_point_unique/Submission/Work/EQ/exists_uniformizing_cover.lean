import Mathlib
import Submission.UnifMain
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Disc
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Topology
import Submission.Work.EQ.UnivCover.Cover
import Submission.Work.EQ.UnivCover.NotCompact
import Submission.Work.EQ.UnivCover.PathConnected
import Submission.Work.EQ.UnivCover.countable_homotopicQuotient
import Submission.Work.EQ.UnivCover.UC_secondCountableTopology
import Submission.Work.EQ.UnivCover.UC_segPt_spec
import Submission.Work.EQ.UnivCover.UC_subsingleton_hom_to_real
import Submission.Work.EQ.UnivCover.exists_chartedSpace_of_isLocalHomeomorph

/-!
# Universal cover + uniformization

A connected, second countable, non-compact Riemann surface `X` is holomorphically covered by `ℂ`
or by the upper half plane `ℍ`.

The proof builds the universal cover `X̃ = UC x₀` (homotopy classes of paths from `x₀`, topologised
by the sheets over disc-like sets), shows that `X̃` is a second countable, connected, non-compact
Hausdorff Riemann surface with a covering projection to `X` and trivial `Hom(π₁, ℝ)`, and applies
the workspace uniformization theorem `Submission.uniformization` to `X̃`.  Composing the covering
projection with the inverse of the resulting biholomorphism gives the required covering map.

The construction lives in `Submission/Work/EQ/UnivCover/`.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology Manifold ContDiff

namespace Work.EQ

open LeanEval.Geometry

/-- **Universal cover + uniformization.** A connected, second countable, non-compact Riemann
surface is holomorphically covered by `ℂ` or by the upper half plane. (Build the universal
cover, pull back the charts, apply `Submission.uniformization`.) -/
theorem exists_uniformizing_cover {X : Type} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold mℂ 1 X]
    (hX : ¬ CompactSpace X) :
    (∃ p : ℂ → X, IsCoveringMap p ∧ MDifferentiable mℂ mℂ p) ∨
      ∃ p : UpperHalfPlane → X, IsCoveringMap p ∧ MDifferentiable mℂ mℂ p := by
  -- `X` is path connected
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  haveI : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  -- the disc-like sets form a basis, and there is a countable cover by them
  have hB : UnivCover.HasDiscBasis X := UnivCover.hasDiscBasis_of_chartedSpace
  obtain ⟨U, hU⟩ := UnivCover.exists_discCover (X := X) hB
  -- choose a base point
  haveI hne : Nonempty X := PathConnectedSpace.nonempty
  let x₀ : X := Classical.choice hne
  -- the universal cover
  have hc : ∀ x : X, Countable (Path.Homotopic.Quotient x₀ x) :=
    fun x => UnivCover.countable_homotopicQuotient (X := X) hU
  haveI : SecondCountableTopology (UnivCover.UC x₀) :=
    UnivCover.UC_secondCountableTopology (X := X) hB hU hc
  haveI : T2Space (UnivCover.UC x₀) := UnivCover.UC_t2Space (X := X) hB
  haveI : PathConnectedSpace (UnivCover.UC x₀) := UnivCover.UC_pathConnectedSpace (X := X) hB
  haveI : ConnectedSpace (UnivCover.UC x₀) := PathConnectedSpace.connectedSpace
  have hcov : IsCoveringMap (UnivCover.UC.proj (x₀ := x₀)) :=
    UnivCover.UC_isCoveringMap_proj (X := X) hB
  -- its complex structure
  obtain ⟨instC, hman, hmdiff⟩ :=
    UnivCover.exists_chartedSpace_of_isLocalHomeomorph (X := X) (S := UnivCover.UC x₀)
      hcov.isLocalHomeomorph
  letI := instC
  haveI hman' : IsManifold mℂ 1 (UnivCover.UC x₀) := hman
  have hmdiff' : MDifferentiable mℂ mℂ (UnivCover.UC.proj (x₀ := x₀)) := hmdiff
  -- it is non-compact and has no non-trivial homomorphism to `ℝ`
  have hnc : ¬ CompactSpace (UnivCover.UC x₀) := UnivCover.UC_not_compactSpace (X := X) hB hX
  haveI hsc : Subsingleton
      (Additive (FundamentalGroup (UnivCover.UC x₀) (UnivCover.UC.base x₀)) →+ ℝ) :=
    UnivCover.UC_subsingleton_hom_to_real (X := X) hB
  -- uniformization of the universal cover
  rcases Submission.uniformization (X := UnivCover.UC x₀) hnc (UnivCover.UC.base x₀) with h | h
  · obtain ⟨e⟩ := h
    refine Or.inl ⟨fun z => UnivCover.UC.proj (x₀ := x₀) (e.symm z), ?_, ?_⟩
    · exact hcov.comp_homeomorph e.symm.toHomeomorph
    · exact hmdiff'.comp (e.symm.mdifferentiable (by simp))
  · obtain ⟨e⟩ := h
    refine Or.inr ⟨fun z => UnivCover.UC.proj (x₀ := x₀) (e.symm z), ?_, ?_⟩
    · exact hcov.comp_homeomorph e.symm.toHomeomorph
    · exact hmdiff'.comp (e.symm.mdifferentiable (by simp))

end Work.EQ
