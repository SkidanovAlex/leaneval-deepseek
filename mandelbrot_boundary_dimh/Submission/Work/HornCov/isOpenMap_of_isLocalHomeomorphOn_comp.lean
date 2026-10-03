import Mathlib

namespace Work.HornCov

/-- **Local step.**  Let `e : OpenPartialHomeomorph B D` be an open partial homeomorphism and
`u : A → B`, `v : A → D` be maps with `v = e ∘ u` pointwise.  If `S` is open and `u` sends `S`
into `e.source`, then `u '' S` is open whenever `v` is an open embedding.

This is the engine of `isOpenMap_of_isLocalHomeomorphOn_comp`: on `e.source` the map `e` is a
homeomorphism, so the open set `v '' S` pulls back to `u '' S`. -/
lemma isOpen_image_of_openPartialHomeomorph_comp {A B D : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace D] {e : OpenPartialHomeomorph B D} {u : A → B}
    {v : A → D} {S : Set A} (hS : IsOpen S) (hsub : ∀ a ∈ S, u a ∈ e.source)
    (hv : ∀ a, e (u a) = v a) (hv' : Topology.IsOpenEmbedding v) : IsOpen (u '' S) := by
  -- On `e.source` the two descriptions `u '' S` and `e.source ∩ e ⁻¹' (v '' S)` agree.
  have hset : u '' S = e.source ∩ (⇑e) ⁻¹' (v '' S) := by
    ext y
    constructor
    · rintro ⟨a, haS, rfl⟩
      exact ⟨hsub a haS, by rw [Set.mem_preimage]; exact ⟨a, haS, (hv a).symm⟩⟩
    · rintro ⟨hy, hyv⟩
      rw [Set.mem_preimage] at hyv
      obtain ⟨a, haS, hav⟩ := hyv
      have hua : u a ∈ e.source := hsub a haS
      have h_eq : e (u a) = e y := by rw [hv a]; exact hav
      exact ⟨a, haS, e.injOn hua hy h_eq⟩
  rw [hset]
  exact e.continuousOn_toFun.isOpen_inter_preimage e.open_source (hv'.isOpenMap S hS)

theorem isOpenMap_of_isLocalHomeomorphOn_comp {A B D : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace D] {q : B → D} {u : A → B} {v : A → D} {s : Set B}
    (hq : IsLocalHomeomorphOn q s) (hus : ∀ a, u a ∈ s) (hu : Continuous u)
    (hv : ∀ a, q (u a) = v a) (hv' : Topology.IsOpenEmbedding v) : IsOpenMap u := by
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨a, haS, rfl⟩
  -- `q` is a homeomorphism on a neighbourhood of `u a`; shrink `S` so that `u` lands there.
  obtain ⟨e, hua, heq⟩ := hq (u a) (hus a)
  have hS' : IsOpen (S ∩ u ⁻¹' e.source) := hS.inter (e.open_source.preimage hu)
  have hsub : ∀ b ∈ S ∩ u ⁻¹' e.source, u b ∈ e.source := fun b hb => hb.2
  have hvpt : ∀ b, e (u b) = v b := fun b => (congrFun heq (u b)).symm.trans (hv b)
  have hopen : IsOpen (u '' (S ∩ u ⁻¹' e.source)) :=
    isOpen_image_of_openPartialHomeomorph_comp hS' hsub hvpt hv'
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨a, ⟨haS, hua⟩, rfl⟩) ?_
  exact Set.image_mono Set.inter_subset_left

end Work.HornCov
