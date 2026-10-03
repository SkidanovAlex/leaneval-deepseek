import Mathlib

set_option linter.style.haveILetI false

/-!
# Restricting a covering map to a clopen subset

If `p : E → B` is a covering map and `C ⊆ E` is clopen, then the restriction of `p` to `C` is
again a covering map, provided the base `B` is locally connected.

The point of the local connectedness hypothesis is that every point `b : B` then admits a
*connected* evenly covered neighbourhood `V`.  Over such a `V` the map `p` trivializes as
`p ⁻¹' V ≃ₜ V × I`, each "sheet" `{v : V} × {i}` being connected; a clopen `C` therefore either
contains a sheet completely or is disjoint from it, so `C ∩ p ⁻¹' V` is a union of whole sheets
and the restricted map still trivializes over `V`, with the (possibly empty) discrete fibre type
`{i // sheet i meets C}`.

Note that no surjectivity of `p` is required: the definition of `IsEvenlyCovered` allows the
empty fibre, which is precisely what happens when no sheet above `V` meets `C`.
-/

namespace Work.Horn.HB

/-- **Shrinking a trivialization to a connected neighbourhood.**

Given a trivialization `H : p ⁻¹' U ≃ₜ U × I` of a continuous map `p` over an open set `U`, and a
point `b ∈ U`, local connectedness of the base produces an open *preconnected* neighbourhood
`V ⊆ U` of `b` together with the restricted trivialization `p ⁻¹' V ≃ₜ V × I`, still compatible
with `p`. -/
lemma exists_preconnected_trivialization {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [LocallyConnectedSpace B] {p : E → B} (hp : Continuous p) {b : B} {U : Set B}
    (hU : IsOpen U) (hbU : b ∈ U)
    {I : Type*} [TopologicalSpace I] (H : p ⁻¹' U ≃ₜ U × I) (hH : ∀ x, (H x).1.1 = p x) :
    ∃ V : Set B, b ∈ V ∧ IsOpen V ∧ IsPreconnected V ∧ V ⊆ U ∧
      ∃ H' : p ⁻¹' V ≃ₜ V × I, ∀ x, (H' x).1.1 = p x := by
  obtain ⟨V, ⟨hVo, hbV, hVc⟩, hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis b).mem_iff.mp (hU.mem_nhds hbU)
  refine ⟨V, hbV, hVo, hVc.isPreconnected, hVU, ?_⟩
  let H' : p ⁻¹' V ≃ₜ V × I :=
    { toFun := fun x => (⟨p x.1, x.2⟩, (H ⟨x.1, hVU x.2⟩).2)
      invFun := fun y => ⟨H.symm (⟨y.1.1, hVU y.1.2⟩, y.2), by
        rw [Set.mem_preimage]
        rw [← hH (H.symm (⟨y.1.1, hVU y.1.2⟩, y.2)), H.apply_symm_apply]
        exact y.1.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        dsimp only
        have hx : (H ⟨x.1, hVU x.2⟩).1 = (⟨p x.1, hVU x.2⟩ : ↥U) := Subtype.ext (hH _)
        have hpair : (H ⟨x.1, hVU x.2⟩) =
            ((⟨p x.1, hVU x.2⟩ : ↥U), (H ⟨x.1, hVU x.2⟩).2) := by rw [← hx]
        rw [← hpair, H.symm_apply_apply]
      right_inv := fun y => by
        apply Prod.ext
        · apply Subtype.ext
          dsimp only
          rw [← hH (H.symm (⟨y.1.1, hVU y.1.2⟩, y.2)), H.apply_symm_apply]
        · dsimp only
          change (H (H.symm (⟨y.1.1, hVU y.1.2⟩, y.2))).2 = y.2
          rw [H.apply_symm_apply]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨H', fun x => rfl⟩

theorem isCoveringMap_subtype_of_isClopen {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [LocallyConnectedSpace B] {p : E → B} (hp : IsCoveringMap p) {C : Set E} (hC : IsClopen C) :
    IsCoveringMap (fun c : C => p c) := by
  intro b
  obtain ⟨hI, U, hbU, hUo, hpUo, H, hH⟩ := hp b
  haveI : DiscreteTopology ↥(p ⁻¹' {b}) := hI
  obtain ⟨V, hbV, hVo, hVpc, hVU, H', hH'⟩ :=
    exists_preconnected_trivialization hp.continuous hUo hbU H hH
  -- transport the picture to the product `↥V × I` via the trivialization `H'`
  let S : Set (↥V × ↥(p ⁻¹' {b})) := {y | (H'.symm y).1 ∈ C}
  have hScl : IsClopen S := hC.preimage (continuous_subtype_val.comp H'.symm.continuous)
  let col : ↥(p ⁻¹' {b}) → Set (↥V × ↥(p ⁻¹' {b})) := fun i => Set.univ ×ˢ ({i} : Set _)
  haveI : PreconnectedSpace ↥V := isPreconnected_iff_preconnectedSpace.mp hVpc
  have hcolpre : ∀ i, IsPreconnected (col i) := fun i =>
    IsPreconnected.prod isPreconnected_univ isPreconnected_singleton
  -- the sheets meeting `C`; a sheet either lies entirely in `C` or is disjoint from it
  let Jsub : Set ↥(p ⁻¹' {b}) := {i | (col i ∩ S).Nonempty}
  have hcolsub : ∀ i, (col i ∩ S).Nonempty → col i ⊆ S := by
    intro i hne
    rcases disjoint_or_subset_of_isClopen (hcolpre i) hScl with h | h
    · rcases hne with ⟨y, hy1, hy2⟩
      exact (h.le_bot ⟨hy1, hy2⟩).elim
    · exact h
  have hS_eq : S = {y : ↥V × ↥(p ⁻¹' {b}) | y.2 ∈ Jsub} := by
    ext y
    constructor
    · intro hy
      exact ⟨y, by simp [col], hy⟩
    · rintro ⟨z, hz1, hz2⟩
      exact hcolsub y.2 ⟨z, hz1, hz2⟩ (by simp [col])
  have hqVo : IsOpen ((fun c : C => p c) ⁻¹' V) := by
    rw [show (fun c : C => p c) ⁻¹' V = Subtype.val ⁻¹' (p ⁻¹' V) from rfl]
    exact (hVo.preimage hp.continuous).preimage continuous_subtype_val
  -- the trivialization of the restricted map over `V`, with fibre `↥Jsub`
  let Hq : (fun c : C => p c) ⁻¹' V ≃ₜ ↥V × ↥Jsub :=
    { toFun := fun c =>
        ((H' ⟨c.1.1, c.2⟩).1,
         ⟨(H' ⟨c.1.1, c.2⟩).2,
          ⟨H' ⟨c.1.1, c.2⟩, by simp [col],
            by change ((H'.symm (H' ⟨c.1.1, c.2⟩)).1 : E) ∈ C
               rw [H'.symm_apply_apply]; exact c.1.2⟩⟩)
      invFun := fun y =>
        ⟨⟨(H'.symm (y.1, y.2.1)).1,
            by exact hcolsub y.2.1 y.2.2 (by simp [col])⟩,
          (H'.symm (y.1, y.2.1)).2⟩
      left_inv := fun c => by
        apply Subtype.ext
        apply Subtype.ext
        dsimp only
        rw [H'.symm_apply_apply]
      right_inv := fun y => by
        apply Prod.ext
        · apply Subtype.ext
          dsimp only
          rw [H'.apply_symm_apply]
        · apply Subtype.ext
          dsimp only
          rw [H'.apply_symm_apply]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact (show IsEvenlyCovered (fun c : C => p c) b ↥Jsub from
      ⟨inferInstance, V, hbV, hVo, hqVo, Hq, fun c => hH' ⟨c.1.1, c.2⟩⟩).to_isEvenlyCovered_preimage

end Work.Horn.HB
