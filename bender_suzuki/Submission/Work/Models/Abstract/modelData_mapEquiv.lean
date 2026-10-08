import Mathlib
import Submission.Work.Models.Abstract.ModelData
import Submission.Work.Models.Abstract.benderPairMapEquiv
import Submission.Work.Models.Abstract.invertedBy_map
import Submission.Work.Models.Port.BenderSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Transport of `ModelData` along a group isomorphism

`Submission.Work.Models.Abstract.benderPairMapEquiv` transports the `BenderPair` part of the
data along `e : G ≃* G'`.  Here we transport the additional `ModelData` fields as well:

* `T` abelian (`hTab`), `w² = 1` (`hww`) and the central-in-`U` property of the involutions of
  `U` (`hUinv`) are elementwise conditions, transported by pulling elements back along `e`;
* `K₀ = J(T,w)` (`hK0`) is transported by `invertedBy_map`;
* cyclicity of `K₀` and `2 ≤ |K₀|` come from `K₀.map e ≃* K₀`;
* `|K₀| = #Inv(B)` needs that `e` maps the involutions of `B` bijectively onto those of
  `B.map e`.

The helper lemmas `involutions_map_mulEquiv`, `ncard_involutions_map_mulEquiv` and
`isCyclic_map_of_injective` are the general transport facts used (the conjugation analogues
are `Work.Models.involutions_conj`, `ncard_involutions_conj` and `isCyclic_map_conj`).
-/

set_option linter.style.haveILetI false

namespace Work.Models.Abstract

variable {G G' : Type*}

section Helpers

variable [Group G] [Group G']

/-- The involutions of `K.map e` are the images of the involutions of `K`. -/
theorem involutions_map_mulEquiv (e : G ≃* G') (K : Subgroup G) :
    Submission.Blueprint.involutions ((K.map e.toMonoidHom : Subgroup G') : Set G')
      = e '' Submission.Blueprint.involutions (K : Set G) := by
  ext x
  constructor
  · rintro ⟨hx, hxord⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨y, ⟨hy, by rw [← MulEquiv.orderOf_eq e y]; exact hxord⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hyord⟩, rfl⟩
    exact ⟨Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, by rw [MulEquiv.orderOf_eq e y]; exact hyord⟩

/-- The number of involutions of a subgroup is unchanged by an isomorphism. -/
theorem ncard_involutions_map_mulEquiv (e : G ≃* G') (K : Subgroup G) :
    (Submission.Blueprint.involutions ((K.map e.toMonoidHom : Subgroup G') : Set G')).ncard
      = (Submission.Blueprint.involutions (K : Set G)).ncard := by
  rw [involutions_map_mulEquiv e K]
  exact Set.ncard_image_of_injective _ e.injective

/-- Cyclicity of a subgroup is preserved by an injective monoid homomorphism. -/
theorem isCyclic_map_of_injective (f : G →* G') (K : Subgroup G)
    (hf : Function.Injective f) (h : IsCyclic K) : IsCyclic (K.map f) := by
  haveI : IsCyclic ↥K := h
  let ee := Subgroup.equivMapOfInjective K f hf
  exact isCyclic_of_surjective ee.toMonoidHom ee.surjective

end Helpers

theorem modelData_mapEquiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (P : Work.Models.ModelData G) (e : G ≃* G') :
    ∃ P' : Work.Models.ModelData G', P'.B = P.B.map e.toMonoidHom ∧
      P'.U = P.U.map e.toMonoidHom ∧ P'.T = P.T.map e.toMonoidHom ∧ P'.w = e P.w ∧
      P'.K0 = P.K0.map e.toMonoidHom := by
  obtain ⟨P₀, hB, hU, hT, hw⟩ := benderPairMapEquiv P.toBenderPair e
  refine ⟨{ toBenderPair := P₀
            K0 := P.K0.map e.toMonoidHom
            hTab := ?_
            hww := ?_
            hK0 := ?_
            hK0cyc := ?_
            hK0card := ?_
            hK0two := ?_
            hUinv := ?_ }, hB, hU, hT, hw, rfl⟩
  · -- `T` abelian: both arguments come from `P.T`, where they commute
    rw [hT]
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, P.hTab x₀ hx₀ y₀ hy₀]
  · -- `w² = 1`
    rw [hw]
    change e.toMonoidHom P.w * e.toMonoidHom P.w = 1
    rw [← map_mul, P.hww, map_one]
  · -- `K₀ = J(T,w) = invertedBy T w`
    rw [hT, hw]
    change ((Subgroup.map e.toMonoidHom P.K0 : Subgroup G') : Set G')
      = Submission.Blueprint.invertedBy (P.T.map e.toMonoidHom) (e.toMonoidHom P.w)
    rw [invertedBy_map e.toMonoidHom P.T P.w e.injective, Subgroup.coe_map, ← P.hK0]
  · -- `K₀` is cyclic
    exact isCyclic_map_of_injective e.toMonoidHom P.K0 e.injective P.hK0cyc
  · -- `|K₀| = #Inv(B)`
    rw [Subgroup.card_map_of_injective e.injective, P.hK0card, hB]
    exact (ncard_involutions_map_mulEquiv e P.B).symm
  · -- `2 ≤ |K₀|`
    rw [Subgroup.card_map_of_injective e.injective]
    exact P.hK0two
  · -- involutions of `U` are central in `U`
    rw [hU]
    intro u hu hu2 v hv
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    have hu₂ : u₀ * u₀ = 1 := by
      apply e.injective
      change e.toMonoidHom (u₀ * u₀) = e.toMonoidHom 1
      rw [map_mul, hu2, map_one]
    rw [← map_mul, ← map_mul, P.hUinv u₀ hu₀ hu₂ v₀ hv₀]

end Work.Models.Abstract
