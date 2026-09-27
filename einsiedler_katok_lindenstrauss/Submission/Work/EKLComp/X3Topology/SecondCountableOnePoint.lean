import Mathlib

namespace Work.EKLComp.X3Topology

open Set Filter Topology

open scoped OnePoint

/-- `OnePoint.infty` neighbourhoods of the form `(↑ '' K n)ᶜ`, where `K` is an exhaustion of `X`
by compact sets, form a basis of neighbourhoods of `∞` in the one-point compactification of a
Hausdorff space `X`.

This is the "at infinity" half of the countable basis of `OnePoint X`. -/
lemma hasBasis_nhds_infty_compl_image (X : Type*) [TopologicalSpace X] [T2Space X]
    (K : CompactExhaustion X) :
    (𝓝 (∞ : OnePoint X)).HasBasis (fun _ : ℕ => True)
      (fun n => ((OnePoint.some '' (K n) : Set (OnePoint X))ᶜ)) := by
  refine Filter.HasBasis.mk (fun t => ⟨fun ht => ?_, fun ht => ?_⟩)
  · obtain ⟨s, hs, hst⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.1 ht
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hs.2
    refine ⟨n, trivial, ?_⟩
    have h1 : (OnePoint.some '' s : Set (OnePoint X))ᶜ ⊆ t := by
      rw [OnePoint.compl_image_coe]
      exact hst
    exact (Set.compl_subset_compl.mpr (Set.image_mono hn)).trans h1
  · obtain ⟨n, -, hn⟩ := ht
    exact Filter.mem_of_superset (IsOpen.mem_nhds
      (OnePoint.isOpen_compl_image_coe.mpr ⟨(K.isCompact n).isClosed, K.isCompact n⟩)
      OnePoint.infty_notMem_image_coe) hn

/-- The one-point compactification of a second countable, locally compact Hausdorff space is
second countable. -/
theorem SecondCountableOnePoint (X : Type*) [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X] : SecondCountableTopology (OnePoint X) := by
  have hSigma : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  let K : CompactExhaustion X := @CompactExhaustion.choice X _ inferInstance hSigma
  have hKb := hasBasis_nhds_infty_compl_image X K
  -- The candidate countable basis: the images of a countable basis of `X`, together with the
  -- complements of the members of a compact exhaustion.
  let b : Set (Set (OnePoint X)) := (fun V => (OnePoint.some '' V : Set (OnePoint X))) ''
      (TopologicalSpace.countableBasis X) ∪
      range (fun n => ((OnePoint.some '' (K n)ᶜ : Set (OnePoint X))) ∪ {∞})
  have hb : TopologicalSpace.IsTopologicalBasis b := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · -- every member of `b` is open
      rintro u (⟨V, hV, rfl⟩ | ⟨n, rfl⟩)
      · exact OnePoint.isOpen_image_coe.mpr (TopologicalSpace.isOpen_of_mem_countableBasis hV)
      · change IsOpen ((OnePoint.some '' (K n)ᶜ : Set (OnePoint X)) ∪ {∞})
        rw [← OnePoint.compl_image_coe]
        exact OnePoint.isOpen_compl_image_coe.mpr ⟨(K.isCompact n).isClosed, K.isCompact n⟩
    · -- every open neighbourhood of a point contains a member of `b`
      intro a u ha hu
      induction a using OnePoint.rec with
      | infty =>
        obtain ⟨n, -, hn⟩ := (hKb.mem_iff).1 (hu.mem_nhds ha)
        exact ⟨(OnePoint.some '' (K n)ᶜ : Set (OnePoint X)) ∪ {∞}, Or.inr ⟨n, rfl⟩, by simp,
          by simpa only [OnePoint.compl_image_coe] using hn⟩
      | coe x =>
        have hU : IsOpen ((OnePoint.some) ⁻¹' u : Set X) := (OnePoint.isOpen_def.mp hu).2
        obtain ⟨V, hV, hxV, hVU⟩ :=
          (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open
            (by simpa using ha) hU
        exact ⟨OnePoint.some '' V, Or.inl ⟨V, hV, rfl⟩, by simpa using hxV, fun y hy => by
          obtain ⟨z, hz, rfl⟩ := hy
          simpa using hVU hz⟩
  exact hb.secondCountableTopology (Set.Countable.union
    ((TopologicalSpace.countable_countableBasis X).image _) (Set.countable_range _))

end Work.EKLComp.X3Topology
