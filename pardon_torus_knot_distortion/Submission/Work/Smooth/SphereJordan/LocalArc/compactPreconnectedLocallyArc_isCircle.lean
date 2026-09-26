import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Develop
import Submission.Work.Smooth.SphereJordan.LocalArc.Limit
import Submission.Work.Smooth.SphereJordan.LocalArc.Param
import Submission.Work.Smooth.SphereJordan.LocalArc.localArcExistsExtensionIcc
import Submission.Work.Smooth.SphereJordan.LocalArc.Branch
import Submission.Work.Smooth.SphereJordan.LocalArc.IsLocallyArcOfIsOpen
import Submission.Work.Smooth.SphereJordan.LocalArc.ArcEnds
import Submission.Work.Smooth.SphereJordan.LocalArc.NestedUnion
import Submission.Work.Smooth.SphereJordan.LocalArc.ChainBound

/-!
# A compact connected locally-arc space is a circle

`compactPreconnectedLocallyArc_isCircle`: a nonempty compact, preconnected, Hausdorff space in
which every point has a neighbourhood homeomorphic to `ℝ` is homeomorphic to the circle, i.e.
admits a `2π`-periodic parametrisation which is injective on `[0, 2π)` and surjective.

The proof combines:

* the chain bound for arc ranges (`ChainBound.chain_bound_of_nested`) with the nested-union lemma
  (`NestedUnion.isArcRange_iUnion_of_monotone`: an increasing sequence of arc ranges through `x₀`
  has a union which is again an arc range), giving a maximal arc range (`MaximalArcRange`);
* maximality forces the two ends of the arc to coincide (`MaximalArcRange.ends_eq_of_isMaximal`),
  and `Ends.exists_circle_param_of_ends_eq` concludes.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X]

theorem compactPreconnectedLocallyArc_isCircle {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [PreconnectedSpace X] [Nonempty X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = Set.univ := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine circle_param_of_nested H x₀ ?_
  intro U hU hmono
  exact ⟨⋃ n, U n, isArcRange_iUnion_of_monotone H U hU hmono,
    fun n => Set.subset_iUnion (fun n => U n) n⟩

end

end Work.Smooth.SphereJordan.LocalArc
