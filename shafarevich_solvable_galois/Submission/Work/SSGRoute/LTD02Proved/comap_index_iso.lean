import Mathlib.GroupTheory.Index
import Mathlib.Topology.Homeomorph.Lemmas
import Submission.Work.SSGRoute.PT.H2Transfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LTD02Proved

set_option maxHeartbeats 800000 in
theorem comap_index_iso {G G' : Type*} [Group G] [TopologicalSpace G] [Group G']
    [TopologicalSpace G'] (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G))
    (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ∃ (e : ↥(U.comap (Φ : G' →* G)) ≃* ↥U),
      IsHomeomorph (e : ↥(U.comap (Φ : G' →* G)) → ↥U) ∧
      (∀ x : ↥(U.comap (Φ : G' →* G)), ((e x : ↥U) : G) = Φ (x : G')) ∧
      IsOpen ((U.comap (Φ : G' →* G) : Subgroup G') : Set G') ∧
      (U.comap (Φ : G' →* G)).index = U.index := by
  -- The group isomorphism sending `x ∈ U.comap Φ` to `Φ x ∈ U`.
  let f : ↥(U.comap (Φ : G' →* G)) →* ↥U :=
    { toFun := fun x => ⟨Φ x, Subgroup.mem_comap.mp x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : Φ a = Φ b := by
      have := congrArg Subtype.val hab
      simpa [f] using this
    exact Subtype.ext (Φ.injective h1)
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨Φ.symm y, ?_⟩, ?_⟩
    · show Φ (Φ.symm y) ∈ U
      rw [MulEquiv.apply_symm_apply]
      exact y.2
    · apply Subtype.ext
      show Φ (Φ.symm y) = (y : G)
      rw [MulEquiv.apply_symm_apply]
  let e : ↥(U.comap (Φ : G' →* G)) ≃* ↥U := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  -- Its values are given by `Φ`.
  have hval : ∀ x : ↥(U.comap (Φ : G' →* G)), ((e x : ↥U) : G) = Φ (x : G') := by
    intro x
    change ((f x : ↥U) : G) = Φ (x : G')
    simp [f]
  -- The homeomorphism `H` underlying `Φ`, restricted to the subtypes,
  -- is a homeomorphism `↥(U.comap Φ) ≃ₜ ↥U` with the same underlying map as `e`.
  let H : G' ≃ₜ G := IsHomeomorph.homeomorph (Φ : G' → G) hΦ
  have hHapply : ∀ x : G', H x = Φ x :=
    fun x => IsHomeomorph.homeomorph_apply (Φ : G' → G) hΦ x
  have hiff : ∀ x : G', x ∈ (U.comap (Φ : G' →* G) : Set G') ↔ H x ∈ U := by
    intro x
    rw [Subgroup.coe_comap, hHapply]
    rfl
  have hEq : (⇑(H.subtype hiff)) = (⇑e) := funext fun x => Subtype.ext (hHapply x)
  have hhomeo : IsHomeomorph (e : ↥(U.comap (Φ : G' →* G)) → ↥U) := by
    have hh : IsHomeomorph (⇑(H.subtype hiff)) := (H.subtype hiff).isHomeomorph
    rwa [hEq] at hh
  refine ⟨e, hhomeo, hval, ?_, ?_⟩
  · -- `U.comap Φ` is the preimage of the open subgroup `U` under the continuous map `Φ`.
    rw [Subgroup.coe_comap]
    exact hΦ.continuous.isOpen_preimage (U : Set G) hU
  · -- The induced bijection of cosets gives equality of indices.
    exact Subgroup.index_comap_of_surjective U Φ.surjective

end Work.SSGRoute.LTD02Proved
