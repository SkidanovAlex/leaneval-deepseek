import Mathlib

namespace Work.Topology.Connected

/-- The connected component inside `S ⊆ ℂ` maps to the connected component inside the image of
`S` under the open embedding `OnePoint.some : ℂ → OnePoint ℂ`.

Suggested proof: `OnePoint.isOpenEmbedding_coe` restricts to a homeomorphism `S ≃ₜ some '' S`, and
`Homeomorph.image_connectedComponentIn`
(`Mathlib.Topology.Homeomorph.Lemmas`) gives the statement for homeomorphisms; the other inclusion
can also be obtained from `ContinuousOn.image_connectedComponentIn_subset` applied to the inverse.
Alternatively, prove it directly from `continuous_coe` / `coe_injective` (the image of a connected
set is connected, and conversely a connected subset of `some '' S` pulls back to a connected subset
of `S` — `some` is an embedding). -/
theorem connectedComponentIn_image_some {S : Set ℂ} {z : ℂ} (hz : z ∈ S) :
    connectedComponentIn (OnePoint.some '' S : Set (OnePoint ℂ)) (OnePoint.some z) =
      OnePoint.some '' connectedComponentIn S z := by
  -- `some : ℂ → OnePoint ℂ` is an inducing map, hence preserves preconnectedness of images.
  have hie : Topology.IsInducing (OnePoint.some : ℂ → OnePoint ℂ) :=
    (OnePoint.isOpenEmbedding_coe.toIsEmbedding).toIsInducing
  refine subset_antisymm ?_ ?_
  · -- The connected component of `some z` inside `some '' S` pulls back to a preconnected
    -- subset of `S` containing `z`.
    have hsub : (connectedComponentIn (OnePoint.some '' S) (OnePoint.some z)) ⊆
        Set.range (OnePoint.some : ℂ → OnePoint ℂ) :=
      (connectedComponentIn_subset _ _).trans (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
    have hpre : IsPreconnected (OnePoint.some ⁻¹'
        (connectedComponentIn (OnePoint.some '' S) (OnePoint.some z))) := by
      rw [← hie.isPreconnected_image, Set.image_preimage_eq_of_subset hsub]
      exact isPreconnected_connectedComponentIn
    have hpreS : OnePoint.some ⁻¹' (connectedComponentIn (OnePoint.some '' S) (OnePoint.some z)) ⊆ S :=
      (Set.preimage_mono (connectedComponentIn_subset _ _)).trans
        (le_of_eq (Set.preimage_image_eq S OnePoint.coe_injective))
    have hzA : OnePoint.some z ∈ connectedComponentIn (OnePoint.some '' S) (OnePoint.some z) :=
      mem_connectedComponentIn (Set.mem_image_of_mem OnePoint.some hz)
    calc connectedComponentIn (OnePoint.some '' S) (OnePoint.some z)
        = OnePoint.some '' (OnePoint.some ⁻¹'
            (connectedComponentIn (OnePoint.some '' S) (OnePoint.some z))) :=
            (Set.image_preimage_eq_of_subset hsub).symm
      _ ⊆ OnePoint.some '' connectedComponentIn S z :=
            Set.image_mono (hpre.subset_connectedComponentIn hzA hpreS)
  · -- Conversely, the image of a connected component is (pre)connected.
    exact (OnePoint.continuous_coe.continuousOn).image_connectedComponentIn_subset hz

end Work.Topology.Connected
