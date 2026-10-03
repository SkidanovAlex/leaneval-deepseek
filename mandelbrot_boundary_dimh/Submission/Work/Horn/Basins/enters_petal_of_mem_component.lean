import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# The index of a point of the parabolic basin is constant on connected components

Let `f` be a map of `ℂ`, `D ⊆ ℂ` and `B := MandelDim.ParabolicBasin f D` its parabolic basin.
Suppose a family `V : Fin q → Set ℂ` is such that

* the index set `ind z := {i | ∃ n, f^[n] z ∈ V i}` of a point of the basin is **locally constant**
  on the basin (`hVindex` — this is the "petal index" local constancy supplied by the horn-map
  analysis),

then `ind` is constant on every connected component of the basin.  Consequently, if `v ∈ V i`, every
`z` in the connected component of the basin through `v` has an iterate in `V i`.

The proof is purely topological: `ind` is locally constant, hence constant on preconnected sets.
The remaining hypotheses (`hVmap`, `hVdisj`, `hVcapture`) are part of the interface but are not
needed here.
-/

namespace Work.Horn.Basins

/-- The set of indices `i` such that the orbit of `z` enters `V i` is locally constant on the
parabolic basin, hence constant on connected components. -/
theorem enters_petal_of_mem_component {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hVmap : ∀ i, ∀ z ∈ V i, f z ∈ V i)
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j))
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ n : ℕ, f^[n] z ∈ ⋃ i, V i)
    (hVindex : ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
      ((∃ n : ℕ, f^[n] z ∈ V i) ↔ (∃ n : ℕ, f^[n] w ∈ V i)))
    {i : Fin q} {v : ℂ} (hv : v ∈ V i) (hvbasin : v ∈ MandelDim.ParabolicBasin f D) :
    ∀ z ∈ connectedComponentIn (MandelDim.ParabolicBasin f D) v, ∃ n : ℕ, f^[n] z ∈ V i := by
  set B : Set ℂ := MandelDim.ParabolicBasin f D with hB
  -- the index-set valued map on the basin
  let G : B → Set (Fin q) := fun y => {j | ∃ n : ℕ, f^[n] (y : ℂ) ∈ V j}
  -- it is locally constant: `hVindex` gives a neighbourhood on which the index sets agree
  have hG : IsLocallyConstant G := by
    rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨U, hUnhds, hUprop⟩ := hVindex y.1 y.2
    rcases mem_nhds_iff.mp hUnhds with ⟨O, hOU, hOopen, hyO⟩
    refine ⟨Subtype.val ⁻¹' O, hOopen.preimage continuous_subtype_val, hyO, ?_⟩
    intro y' hy'
    exact Set.ext fun j => (hUprop y' (hOU hy') j).symm
  intro z hz
  -- a locally constant function is constant on preconnected sets
  rw [connectedComponentIn_eq_image hvbasin] at hz
  rcases hz with ⟨t, ht, htz⟩
  have heq : G ⟨v, hvbasin⟩ = G t :=
    hG.apply_eq_of_isPreconnected (s := connectedComponent (⟨v, hvbasin⟩ : B))
      isPreconnected_connectedComponent mem_connectedComponent ht
  -- `i` is in the index set of `v` because of `hv` itself (n = 0)
  have hmem : i ∈ G ⟨v, hvbasin⟩ := ⟨0, by simpa using hv⟩
  rw [heq] at hmem
  simpa [G, htz] using hmem

end Work.Horn.Basins
