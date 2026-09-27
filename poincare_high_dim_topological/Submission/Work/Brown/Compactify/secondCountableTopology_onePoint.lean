import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Compactify

open Set Filter Topology

/-- If `X` is second countable and its closed compact subsets admit a countable cofinal family,
then the one-point compactification of `X` is second countable: the images of a countable basis of
`X` together with the complements (in `OnePoint X`) of the cofinal family form a countable basis. -/
theorem secondCountableTopology_onePoint_of_cofinal {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X]
    (hC : ∃ C : ℕ → Set X, (∀ n, IsClosed (C n) ∧ IsCompact (C n)) ∧
      ∀ K : Set X, IsClosed K → IsCompact K → ∃ n, K ⊆ C n) :
    SecondCountableTopology (OnePoint X) := by
  obtain ⟨C, hCcl, hCcof⟩ := hC
  have hbidx := TopologicalSpace.isBasis_countableBasis X
  let b : Set (Set (OnePoint X)) :=
    (fun U => (↑) '' U) '' TopologicalSpace.countableBasis X ∪
      (fun n : ℕ => (((↑) '' C n : Set (OnePoint X))ᶜ)) '' Set.univ
  have hbcount : b.Countable := by
    refine Countable.union ?_ ?_
    · exact (TopologicalSpace.countable_countableBasis X).image _
    · rw [Set.image_univ]
      exact countable_range _
  refine TopologicalSpace.IsTopologicalBasis.secondCountableTopology ?_ hbcount
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro v hv
    rcases hv with ⟨U, hU, rfl⟩ | ⟨n, -, rfl⟩
    · exact OnePoint.isOpen_image_coe.2 (TopologicalSpace.isOpen_of_mem_countableBasis hU)
    · exact OnePoint.isOpen_compl_image_coe.2 ⟨(hCcl n).1, (hCcl n).2⟩
  · intro a u hau hu
    induction a using OnePoint.rec with
    | infty =>
      obtain ⟨hcomp, hopen⟩ := (OnePoint.isOpen_iff_of_mem' hau).mp hu
      have hcl : IsClosed (((↑)⁻¹' u : Set X))ᶜ := hopen.isClosed_compl
      obtain ⟨n, hn⟩ := hCcof (((↑)⁻¹' u : Set X))ᶜ hcl hcomp
      refine ⟨((↑) '' C n : Set (OnePoint X))ᶜ, ?_, ?_, ?_⟩
      · exact Or.inr ⟨n, Set.mem_univ n, rfl⟩
      · exact OnePoint.infty_notMem_image_coe
      · intro y hy
        induction y using OnePoint.rec with
        | infty => exact hau
        | coe z =>
          have hz : z ∉ C n := fun hz => hy (Set.mem_image_of_mem _ hz)
          have hz2 : z ∉ (((↑)⁻¹' u : Set X))ᶜ := fun h => hz (hn h)
          exact Set.mem_preimage.mp (not_not.mp hz2)
    | coe x =>
      have hopen : IsOpen ((↑)⁻¹' u : Set X) := (OnePoint.isOpen_def.mp hu).2
      obtain ⟨U, hU, hxU, hUu⟩ := hbidx.exists_subset_of_mem_open hau hopen
      refine ⟨(↑) '' U, ?_, ?_, ?_⟩
      · exact Or.inl ⟨U, hU, rfl⟩
      · exact ⟨x, hxU, rfl⟩
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact Set.mem_preimage.mp (hUu hz)

/-- The one-point compactification of a second countable, locally compact Hausdorff space is
second countable.  (The Hausdorff hypothesis is necessary: without it, a compact set need not be
closed and the closed compact sets need not be cofinal.)

This is the instance needed to apply `Work.Brown.Engine.sphere_of_collapse_sequence` to
`OnePoint X`, where `X` is a monotone union of open cells. -/
theorem secondCountableTopology_onePoint {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SigmaCompactSpace X] [SecondCountableTopology X] :
    SecondCountableTopology (OnePoint X) := by
  haveI : WeaklyLocallyCompactSpace X := inferInstance
  let K : CompactExhaustion X := CompactExhaustion.choice X
  exact secondCountableTopology_onePoint_of_cofinal
    ⟨fun n => K n, fun n => ⟨(K.isCompact n).isClosed, K.isCompact n⟩,
      fun C _ hC => K.exists_superset_of_isCompact hC⟩

end Work.Brown.Compactify
