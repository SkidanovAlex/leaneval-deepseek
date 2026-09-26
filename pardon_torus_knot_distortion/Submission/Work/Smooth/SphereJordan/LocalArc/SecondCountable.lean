import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic

/-!
# A compact locally-arc space is second countable

`secondCountableTopology_of_isLocallyArc`: a compact space in which every point has a
neighbourhood homeomorphic to `ℝ` is second countable.  The chart neighbourhoods form an open
cover, compactness gives a finite subcover, and a countable open cover by second countable open
subspaces gives a second countable space (`secondCountableTopology_of_countable_cover`).
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function

open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/-- **A compact locally-arc space is second countable.** -/
theorem secondCountableTopology_of_isLocallyArc
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) : SecondCountableTopology X := by
  classical
  let c : ∀ x : X, Work.Smooth.SphereJordan.ArcChart X x := fun x => Classical.choice (H x)
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, (c x).V := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, (c y).mem_V⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (c x).V)
    (fun x => (c x).isOpen_V) hcover
  haveI : Fintype ↥t := Finset.fintypeCoeSort t
  haveI : ∀ x : ↥t, SecondCountableTopology ↥((c x.1).V) :=
    fun x => (c x.1).homeo.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun x : ↥t => (c x.1).V) (fun x => (c x.1).isOpen_V) ?_
  rw [eq_univ_iff_forall]
  intro y
  have hy : y ∈ ⋃ x ∈ t, (c x).V := ht (Set.mem_univ y)
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩

end

end Work.Smooth.SphereJordan.LocalArc
