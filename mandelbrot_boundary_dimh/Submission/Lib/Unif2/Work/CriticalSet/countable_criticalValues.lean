import Submission.Lib.Unif2.Work.CriticalSet.Defs
import Submission.Lib.Unif2.Work.CriticalSet.criticalSet_isLocallyFinite

/-!
# The critical points and critical values of a Green function are countable

A discrete subset of a second countable space is countable.  Applying this to the critical set of a
Green function (discrete on the punctured surface by
`Work.CriticalSet.criticalSet_isDiscreteIn`) gives:

* `Work.CriticalSet.countable_criticalSet_of_hasGreenFunctionWeak` — the critical points of the
  Green function are countable;
* `Work.CriticalSet.countable_criticalValues_of_hasGreenFunctionWeak` — so are its critical values.

This is what makes regular values plentiful: the complement of a countable subset of `ℝ` is dense.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.CriticalSet

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A set which is discrete in `U` (every point of `U` has a neighbourhood meeting it at most in
that point) and contained in `U` is a discrete subspace. -/
theorem IsDiscreteIn.isDiscrete {S U : Set X} (h : IsDiscreteIn S U) (hSU : S ⊆ U) :
    IsDiscrete S := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  obtain ⟨V, hV, hVsub⟩ := h y (hSU hy)
  obtain ⟨u, huV, huopen, hyu⟩ := mem_nhds_iff.mp hV
  refine ⟨u, huopen, ?_⟩
  ext z
  constructor
  · rintro ⟨hzu, hzS⟩
    exact hVsub ⟨hzS, huV hzu⟩
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hyu, hy⟩

/-- **A set discrete in `U ⊆ X` is countable**, when `X` is second countable (hence hereditarily
Lindelöf: any discrete subset of a Lindelöf space is countable). -/
theorem countable_of_isDiscreteIn [SecondCountableTopology X] {S U : Set X}
    (h : IsDiscreteIn S U) (hSU : S ⊆ U) : S.Countable :=
  (HereditarilyLindelofSpace.isLindelof S).countable_of_isDiscrete (h.isDiscrete hSU)

/-- **The critical set of a Green function is countable.** -/
theorem countable_criticalSet_of_hasGreenFunctionWeak [SecondCountableTopology X] {z₀ : X}
    {E : X → ℝ} (hE : Submission.HasGreenFunctionWeak z₀ E)
    (hnlc : NotLocallyConstantOn E (punctured z₀)) :
    (criticalSet E (punctured z₀)).Countable :=
  countable_of_isDiscreteIn
    (criticalSet_isDiscreteIn (isOpen_punctured z₀) hE.2.1 hnlc) fun _ hx => hx.1

/-- **The critical values of a Green function are countable.** -/
theorem countable_criticalValues_of_hasGreenFunctionWeak [SecondCountableTopology X] {z₀ : X}
    {E : X → ℝ} (hE : Submission.HasGreenFunctionWeak z₀ E)
    (hnlc : NotLocallyConstantOn E (punctured z₀)) :
    (E '' criticalSet E (punctured z₀)).Countable :=
  (countable_criticalSet_of_hasGreenFunctionWeak hE hnlc).image E

end Work.CriticalSet
