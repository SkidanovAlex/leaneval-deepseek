import Mathlib

namespace Work.Drive

open Manifold Topology Set OpenPartialHomeomorph

/-- Two partial inverses `L`, `L'` of the same injective map `f` (meaning `⇑L.symm = f = ⇑L'.symm`)
give, for any two charts `C`, `C'` on the source of `f`, a transition
`(L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')` which is the transition `C.symm ≫ₕ C'` read on a smaller open set.

Concretely: if `C.symm ≫ₕ C'` belongs to a restriction-closed structure groupoid `G`, then so does
`(L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')`.  This is the computation underlying the fact that a `ChartedSpace`
structure transported along a homeomorphism is a smooth manifold whenever the original one is. -/
theorem mem_groupoid_of_localInverses {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (G : StructureGroupoid Z) [ClosedUnderRestriction G]
    {f : X → Y} (hf : Function.Injective f)
    {L L' : OpenPartialHomeomorph Y X} (hL : ⇑L.symm = f) (hL' : ⇑L'.symm = f)
    {C C' : OpenPartialHomeomorph X Z} (hC : C.symm ≫ₕ C' ∈ G) :
    (L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C') ∈ G := by
  -- Description of the source of the composite transition, in adapted coordinates.
  have hsimp : ∀ h, h ∈ ((L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')).source →
      ((h ∈ C.symm.source ∧ ⇑C.symm h ∈ L.symm.source) ∧
        f (⇑C.symm h) ∈ L'.source ∧ ⇑L' (f (⇑C.symm h)) ∈ C'.source) := by
    intro h hh
    simpa only [OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, Set.mem_inter_iff, Set.mem_preimage,
      OpenPartialHomeomorph.coe_trans, Function.comp_apply, hL] using hh
  -- The two partial inverses agree on the relevant domain.
  have hstep : ∀ h ∈ ((L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')).source,
      ⇑L' (f (⇑C.symm h)) = ⇑C.symm h := by
    intro h hh
    have hmem : f (⇑C.symm h) ∈ L'.source := (hsimp h hh).2.1
    have h1 : ⇑L'.symm (⇑L' (f (⇑C.symm h))) = f (⇑C.symm h) := L'.left_inv hmem
    rw [hL'] at h1
    exact hf h1
  have hsub : ((L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')).source ⊆ (C.symm ≫ₕ C').source := by
    intro h hh
    have hCt : h ∈ C.target := (hsimp h hh).1.1
    have hC's : ⇑C.symm h ∈ C'.source := by
      rw [← hstep h hh]
      exact (hsimp h hh).2.2
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hCt, hC's⟩
  have heq : Set.EqOn (⇑(C.symm ≫ₕ C')) (⇑((L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')))
      ((L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')).source := by
    intro h hh
    have h3 : ⇑L' (f (⇑C.symm h)) = ⇑C.symm h := hstep h hh
    change ⇑C' (⇑C.symm h) = ⇑C' (⇑L' (⇑L.symm (⇑C.symm h)))
    rw [hL, h3]
  have hkey : ((L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')).restr
      ((L ≫ₕ C).symm ≫ₕ (L' ≫ₕ C')).source ∈ G :=
    StructureGroupoid.restr_mem_of_eqOn hC (OpenPartialHomeomorph.open_source _) heq
      (fun _ hh => hsub hh.1)
  exact G.locality fun h hh => ⟨_, OpenPartialHomeomorph.open_source _, hh, hkey⟩

theorem homeomorph_isManifold {H : Type*} [TopologicalSpace H] {M M' : Type*}
    [TopologicalSpace M] [TopologicalSpace M'] [ChartedSpace H M]
    (e : M ≃ₜ M') {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) {n : WithTop ℕ∞} [IsManifold I n M] :
    @IsManifold 𝕜 _ E _ _ H _ I n M' _ (Homeomorph.chartedSpace e) := by
  let : ChartedSpace H M' := Homeomorph.chartedSpace e
  refine IsManifold.mk' I n M' (gr := ?_)
  refine ⟨fun {c c'} hc hc' => ?_⟩
  -- Unfold the transported atlas: its charts are `localInverseAt x ≫ₕ chartAt H x`.
  have hatlas : ∀ c : OpenPartialHomeomorph M' H, c ∈ atlas H M' ↔
      ∃ q : M', (e.isLocalHomeomorph.localInverseAt (e.surjective.hasRightInverse.choose q)).trans
        (chartAt H (e.surjective.hasRightInverse.choose q)) = c := fun c => Iff.rfl
  obtain ⟨q, hq⟩ := (hatlas c).mp hc
  obtain ⟨q', hq'⟩ := (hatlas c').mp hc'
  rw [← hq, ← hq']
  -- Both charts are `L ≫ₕ C` for `L` a partial inverse of `e` and `C` a chart of `M`,
  -- so the transition between them is a transition of `M` restricted to a smaller open set.
  refine mem_groupoid_of_localInverses (contDiffGroupoid n I) e.injective
    (IsLocalHomeomorph.localInverseAt_symm e.isLocalHomeomorph _)
    (IsLocalHomeomorph.localInverseAt_symm e.isLocalHomeomorph _) ?_
  exact StructureGroupoid.compatible (contDiffGroupoid n I) (chart_mem_atlas H _) (chart_mem_atlas H _)

end Work.Drive
