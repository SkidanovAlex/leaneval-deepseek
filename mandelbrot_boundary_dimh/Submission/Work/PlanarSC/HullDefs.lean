import Mathlib
import Submission.Work.PlanarSC.PolyDefs
import Submission.Lib.Unif2.Commons.Topology.Jordan.compl_compact_unique_unbounded

/-!
# The complementary-component hull ("filling") of a closed subset of the plane

For `A ⊆ ℂ`, `compHull A` is the set of points whose connected component in `Aᶜ` is *bounded*.
For closed `A` this is `A` together with all the bounded components of `Aᶜ` — the classical
"filling in of the holes" of a compact plane set.  The two facts that make it useful are recorded as
the delegated lemmas `Work.PlanarSC.{exists_finset_compHull_eq, isPreconnected_compHull,
isPreconnected_compl_compHull, compHull_subset_of_no_bounded_complement}`:

* if `A` is a finite union of dyadic cells then so is `compHull A`;
* if `A` is preconnected (and nonempty) then so is `compHull A`;
* `(compHull A)ᶜ` is preconnected as soon as `A` is compact;
* if `A ⊆ U` and `U` has no bounded complementary component, then `compHull A ⊆ U`.
-/

open Set

namespace Work.PlanarSC

/-- The **hull** of `A ⊆ ℂ`: the set of points whose connected component in `Aᶜ` is bounded. -/
def compHull (A : Set ℂ) : Set ℂ := {z : ℂ | Bornology.IsBounded (connectedComponentIn Aᶜ z)}

@[simp]
theorem mem_compHull {A : Set ℂ} {z : ℂ} :
    z ∈ compHull A ↔ Bornology.IsBounded (connectedComponentIn Aᶜ z) := Iff.rfl

theorem notMem_compHull {A : Set ℂ} {z : ℂ} :
    z ∉ compHull A ↔ ¬ Bornology.IsBounded (connectedComponentIn Aᶜ z) := Iff.rfl

theorem compl_compHull (A : Set ℂ) :
    (compHull A)ᶜ = {z : ℂ | ¬ Bornology.IsBounded (connectedComponentIn Aᶜ z)} := by
  rw [compHull, Set.compl_setOf]

/-- Every point of `A` lies in its hull: if `z ∈ A` then `Aᶜ` contains no component of `z`. -/
theorem subset_compHull {A : Set ℂ} : A ⊆ compHull A := by
  intro z hz
  rw [mem_compHull, connectedComponentIn_eq_empty (by simpa using hz)]
  exact Bornology.isBounded_empty

end Work.PlanarSC
