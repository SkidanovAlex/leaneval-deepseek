import Mathlib

/-!
# Stability of an open condition along the slice of a closed relation (the `hV` tube lemma)

The counting route to Hugelmeyer's order function (`Work.Drive.chainParity`) instantiates the
triple-intersection engine with three *swept chains* obtained from three plane presentations by a
projective-class perturbation `Work.Drive.linCapping (A k)`.  One of the engine's four hypotheses is
the general-position condition `hV` at every **triple point** `x` of the three sweeps:

> `(planeClassDeriv 0 x).range ⊓ (planeClassDeriv 1 x).range ⊓ (planeClassDeriv 2 x).range = ⊥`,

a condition that is (i) defined only at triple points (the three sweep values must coincide, so that
their class derivatives live in one tangent space), and (ii) **open** in its data.

This file proves the topological fact that makes `hV` *robust*: if `hV` holds at every triple point
of the *unperturbed* chains, then it holds at every triple point of every *sufficiently small*
perturbation.  Concretely, let `Z ⊆ T × X` be the closed set of pairs `(A, x)` at which `x` is a
triple point of the configuration `A` (here `T` is the perturbation space, `X` the compact parameter
cube), and let `G ⊆ T × X` be the set of pairs at which the (open) condition `hV` holds.  Then

> `Z ∩ (K ×ˢ univ) ⊆ G` for a compact `K`  ⟹  `∃ U open ⊇ K, Z ∩ (U ×ˢ univ) ⊆ G`.

The proof is the classical tube argument: the bad set `Z ∩ Gᶜ` is closed and misses the slice
`K ×ˢ univ`; compactness of `X` upgrades the pointwise product neighbourhoods (of open `s := (Z ∩ Gᶜ)ᶜ`
at the points of the slice) to a *uniform* product neighbourhood `U₀ ×ˢ univ ⊆ s` of each single point,
and then compactness of `K` turns the family `{U₀}` into one neighbourhood of `K`.

Two uses in the design:

* **perturbation robustness**: a perturbation may be spent on the *face* condition (`hface`) or on the
  seam without losing the general position already established for the unperturbed chains;
* **locality**: the argument is applied to the *intrinsic* (chart-free) form of `hV`
  (`Work.Drive.planeClassDeriv_range_generalPosition_iff`), which is insensitive to the locally
  constant — but not globally defined — chart index of the common class of a triple point.
-/

namespace Work.Drive

open Set Filter

/-- **A product neighbourhood of a point that lies in an open set along a whole vertical fibre.**
If `s` is open and `{t} ×ˢ univ ⊆ s` and `X` is compact, then there is an open `U ∋ t` with
`U ×ˢ univ ⊆ s`. -/
theorem exists_isOpen_prod_univ_subset {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [CompactSpace X] {s : Set (T × X)} (hs : IsOpen s) {t : T}
    (ht : ({t} ×ˢ (Set.univ : Set X)) ⊆ s) :
    ∃ U : Set T, IsOpen U ∧ t ∈ U ∧ U ×ˢ (Set.univ : Set X) ⊆ s := by
  -- pointwise product neighbourhoods
  have hpt : ∀ x : X, ∃ u : Set T, ∃ v : Set X,
      IsOpen u ∧ IsOpen v ∧ t ∈ u ∧ x ∈ v ∧ u ×ˢ v ⊆ s :=
    fun x => isOpen_prod_iff.mp hs t x (ht ⟨rfl, trivial⟩)
  choose u v h using hpt
  -- a finite subcover of the vertical neighbourhoods
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := X))
    (fun x : X => v x) (fun x => (h x).2.1) (fun x _ => Set.mem_iUnion.mpr ⟨x, (h x).2.2.2.1⟩)
  refine ⟨⋂ x ∈ F, u x, isOpen_biInter_finset fun x _ => (h x).1, ?_, ?_⟩
  · exact Set.mem_iInter₂.mpr fun x _ => (h x).2.2.1
  · rintro ⟨t', x'⟩ ⟨ht', -⟩
    obtain ⟨x₀, hx₀F, hx₀⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x'))
    exact (h x₀).2.2.2.2 ⟨Set.mem_iInter₂.mp ht' x₀ hx₀F, hx₀⟩


/-- **A product neighbourhood of a point that lies in an open set along a compact fibre.**  The compact
set version of `Work.Drive.exists_isOpen_prod_univ_subset`: `{t} ×ˢ K₀ ⊆ s` with `K₀` compact gives an
open `U ∋ t` with `U ×ˢ K₀ ⊆ s`. -/
theorem exists_isOpen_prod_subset {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
    {K₀ : Set X} (hK₀ : IsCompact K₀) {s : Set (T × X)} (hs : IsOpen s) {t : T}
    (ht : ({t} ×ˢ K₀) ⊆ s) :
    ∃ U : Set T, IsOpen U ∧ t ∈ U ∧ U ×ˢ K₀ ⊆ s := by
  have hpt : ∀ i : K₀, ∃ u : Set T, ∃ v : Set X,
      IsOpen u ∧ IsOpen v ∧ t ∈ u ∧ (i : X) ∈ v ∧ u ×ˢ v ⊆ s :=
    fun i => isOpen_prod_iff.mp hs t i (ht ⟨rfl, i.2⟩)
  choose u v h using hpt
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover hK₀ (fun i : K₀ => v i)
    (fun i => (h i).2.1)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (h ⟨x, hx⟩).2.2.2.1⟩)
  refine ⟨⋂ i ∈ F, u i, isOpen_biInter_finset fun i _ => (h i).1, ?_, ?_⟩
  · exact Set.mem_iInter₂.mpr fun i _ => (h i).2.2.1
  · rintro ⟨t', x'⟩ ⟨ht', hx'⟩
    obtain ⟨i, hiF, hi⟩ := Set.mem_iUnion₂.mp (hF hx')
    exact (h i).2.2.2.2 ⟨Set.mem_iInter₂.mp ht' i hiF, hi⟩

/-- **The tube lemma for the slice of a closed relation over a compact parameter set and a compact
fibre.**  The compact-set form of `Work.Drive.exists_prod_nhds_subset_of_isCompact`, which is what the
counting route needs: there, the parameter space is `ℝ⁹` (not compact) and the relevant fibre is the
*box* `Submission.Drive.unitBox 8`. -/
theorem exists_prod_nhds_subset_of_isCompact_set {T X : Type*} [TopologicalSpace T]
    [TopologicalSpace X] {Z G : Set (T × X)} (hZ : IsClosed Z) (hG : IsOpen G)
    {K : Set T} (hK : IsCompact K) {K₀ : Set X} (hK₀ : IsCompact K₀)
    (hsub : Z ∩ (K ×ˢ K₀) ⊆ G) :
    ∃ U : Set T, K ⊆ U ∧ IsOpen U ∧ Z ∩ (U ×ˢ K₀) ⊆ G := by
  set s : Set (T × X) := (Z ∩ Gᶜ)ᶜ with hsdef
  have hsopen : IsOpen s := (hZ.inter hG.isClosed_compl).isOpen_compl
  have hsub' : K ×ˢ K₀ ⊆ s := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [hsdef, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
    exact fun hZt hGt => hGt (hsub ⟨hZt, ht, hx⟩)
  have hpt : ∀ i : K, ∃ U : Set T, IsOpen U ∧ (i : T) ∈ U ∧ U ×ˢ K₀ ⊆ s :=
    fun i => exists_isOpen_prod_subset hK₀ hsopen (t := (i : T)) fun p hp =>
      hsub' ⟨(Set.mem_singleton_iff.mp hp.1).symm ▸ i.2, hp.2⟩
  choose U hU using hpt
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover hK (fun i : K => U i)
    (fun i => (hU i).1) (fun t ht => Set.mem_iUnion.mpr ⟨⟨t, ht⟩, (hU ⟨t, ht⟩).2.1⟩)
  refine ⟨⋃ i ∈ F, U i, ?_, isOpen_biUnion fun i _ => (hU i).1, ?_⟩
  · intro t ht
    obtain ⟨i, hiF, hti⟩ := Set.mem_iUnion₂.mp (hF ht)
    exact Set.mem_iUnion₂.mpr ⟨i, hiF, hti⟩
  · rintro p ⟨hpZ, hpU, hpK⟩
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hpU
    by_contra hcon
    exact ((hU i).2.2 ⟨hi, hpK⟩) ⟨hpZ, hcon⟩

/-- **The tube lemma for the slice of a closed relation, in the form used by the `hV` stability
argument.**

If `Z ⊆ T × X` is closed, `G ⊆ T × X` is open, `X` is compact, `K ⊆ T` is compact and the whole slice
of `Z` over `K` lies in `G`, then an open neighbourhood `U ×ˢ X` of that slice lies in `G`. -/
theorem exists_prod_nhds_subset_of_isCompact {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [CompactSpace X] {Z G : Set (T × X)} (hZ : IsClosed Z) (hG : IsOpen G)
    {K : Set T} (hK : IsCompact K) (hsub : Z ∩ (K ×ˢ (Set.univ : Set X)) ⊆ G) :
    ∃ U : Set T, K ⊆ U ∧ IsOpen U ∧ Z ∩ (U ×ˢ (Set.univ : Set X)) ⊆ G := by
  set s : Set (T × X) := (Z ∩ Gᶜ)ᶜ with hsdef
  have hsopen : IsOpen s := (hZ.inter hG.isClosed_compl).isOpen_compl
  have hsub' : K ×ˢ (Set.univ : Set X) ⊆ s := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    rw [hsdef, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
    exact fun hZt hGt => hGt (hsub ⟨hZt, ht, trivial⟩)
  -- each point of `K` has a product neighbourhood contained in `s`
  have hpt : ∀ i : K, ∃ U : Set T, IsOpen U ∧ (i : T) ∈ U ∧ U ×ˢ (Set.univ : Set X) ⊆ s :=
    fun i => exists_isOpen_prod_univ_subset hsopen (t := (i : T)) fun p hp =>
      hsub' ⟨(Set.mem_singleton_iff.mp hp.1).symm ▸ i.2, hp.2⟩
  choose U hU using hpt
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover hK (fun i : K => U i)
    (fun i => (hU i).1) (fun t ht => Set.mem_iUnion.mpr ⟨⟨t, ht⟩, (hU ⟨t, ht⟩).2.1⟩)
  refine ⟨⋃ i ∈ F, U i, ?_, isOpen_biUnion fun i _ => (hU i).1, ?_⟩
  · intro t ht
    obtain ⟨i, hiF, hti⟩ := Set.mem_iUnion₂.mp (hF ht)
    exact Set.mem_iUnion₂.mpr ⟨i, hiF, hti⟩
  · rintro p ⟨hpZ, hpU, -⟩
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hpU
    by_contra hcon
    exact ((hU i).2.2 ⟨hi, trivial⟩) ⟨hpZ, hcon⟩

/-- **Stability of an open condition under a small perturbation of the chain.**  The special case
`K = {1}` of `Work.Drive.exists_prod_nhds_subset_of_isCompact`: if the open condition holds along the
whole slice over the base parameter, it holds for every sufficiently small perturbation. -/
theorem exists_nhds_prod_subset_of_slice_subset {T X : Type*} [TopologicalSpace T]
    [TopologicalSpace X] [CompactSpace X] {Z G : Set (T × X)} (hZ : IsClosed Z) (hG : IsOpen G)
    {t₀ : T} (hsub : Z ∩ ({t₀} ×ˢ (Set.univ : Set X)) ⊆ G) :
    ∃ U ∈ nhds t₀, Z ∩ (U ×ˢ (Set.univ : Set X)) ⊆ G := by
  obtain ⟨U, hKU, hUopen, hsubU⟩ :=
    exists_prod_nhds_subset_of_isCompact hZ hG (isCompact_singleton (x := t₀)) hsub
  exact ⟨U, hUopen.mem_nhds (hKU (Set.mem_singleton t₀)), hsubU⟩

end Work.Drive
