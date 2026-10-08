import Mathlib
import Submission.Work.CORE2B.HallPerPrime_Xodd

/-!
# `|O_{2'}(K^e)| = |O_{2'}(K)|` for an automorphism `e` of `G`

`Work.GW2.oddCoreIn K = (O_{2'}(↥K)).map K.subtype` is the odd core `O(K)` of the subgroup
`K ≤ G`, transported into `G`.  Multiplication by an automorphism `e : MulAut G` is an
isomorphism `↥K ≃* ↥(K.map e.toMonoidHom)`, and `O(-)` is characteristic, so it transports:

* `oddCore_map_mulEquiv` — for any group isomorphism `φ : X ≃* Y`, `O(X)` maps onto `O(Y)`
  (both inclusions come from maximality of `O` plus the fact that `Nat.card` is preserved by an
  isomorphism, so the image of `O` is a normal odd-order subgroup);
* `oddCoreIn_eq_map_mulAut` — consequently
  `O(K.map e) = (O(K)).map e` as subgroups of `G`;
* `oddCoreIn_card_map_mulAut` — taking cardinalities (an injective homomorphism preserves
  `Nat.card` of a subgroup) gives the requested equality.
-/

namespace Work.CORE2B

open Subgroup

/-- One inclusion of the transport of `O(-)` along a group isomorphism: the image of `O(X)` is
normal in `Y` (the isomorphism is surjective) and has odd order (it is injective), so maximality
of `O(Y)` puts it inside `O(Y)`. -/
private theorem oddCore_map_le {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : X ≃* Y) : (Work.GW2.oddCore X).map φ.toMonoidHom ≤ Work.GW2.oddCore Y := by
  have hN : ((Work.GW2.oddCore X).map φ.toMonoidHom).Normal :=
    (Work.GW2.oddCore_normal X).map φ.toMonoidHom φ.surjective
  have hodd : Odd (Nat.card ↥((Work.GW2.oddCore X).map φ.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact oddCore_odd
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hN, hodd⟩)

/-- `O(-)` is transported by a group isomorphism: `O(X)` maps onto `O(Y)`. -/
theorem oddCore_map_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : X ≃* Y) : (Work.GW2.oddCore X).map φ.toMonoidHom = Work.GW2.oddCore Y := by
  refine le_antisymm (oddCore_map_le φ) ?_
  calc Work.GW2.oddCore Y
      = (Work.GW2.oddCore Y).map (MonoidHom.id Y) := (Subgroup.map_id _).symm
    _ = (Work.GW2.oddCore Y).map (φ.toMonoidHom.comp φ.symm.toMonoidHom) := by
          congr 1; ext x; simp
    _ = ((Work.GW2.oddCore Y).map φ.symm.toMonoidHom).map φ.toMonoidHom :=
          (Subgroup.map_map _ _ _).symm
    _ ≤ (Work.GW2.oddCore X).map φ.toMonoidHom := Subgroup.map_mono (oddCore_map_le φ.symm)

/-- `O(K)` is transported by an automorphism `e` of `G`: `O(K.map e) = (O(K)).map e`.  The
isomorphism `↥K ≃* ↥(K.map e.toMonoidHom)` provided by `Subgroup.equivMapOfInjective` carries
`O(↥K)` onto `O(↥(K.map e))`, and pushing forward along the two subtypes gives the claim. -/
theorem oddCoreIn_eq_map_mulAut {G : Type} [Group G] [Finite G] (e : MulAut G) (K : Subgroup G) :
    Work.GW2.oddCoreIn (K.map e.toMonoidHom) = (Work.GW2.oddCoreIn K).map e.toMonoidHom := by
  let ψ : ↥K ≃* ↥(K.map e.toMonoidHom) := K.equivMapOfInjective e.toMonoidHom e.injective
  have hψ : (Work.GW2.oddCore ↥K).map ψ.toMonoidHom = Work.GW2.oddCore ↥(K.map e.toMonoidHom) :=
    oddCore_map_mulEquiv ψ
  have hcomp : ((K.map e.toMonoidHom).subtype.comp ψ.toMonoidHom : ↥K →* G)
      = e.toMonoidHom.comp K.subtype := by
    ext x
    rfl
  calc Work.GW2.oddCoreIn (K.map e.toMonoidHom)
      = (Work.GW2.oddCore ↥(K.map e.toMonoidHom)).map (K.map e.toMonoidHom).subtype := rfl
    _ = ((Work.GW2.oddCore ↥K).map ψ.toMonoidHom).map (K.map e.toMonoidHom).subtype := by rw [hψ]
    _ = (Work.GW2.oddCore ↥K).map ((K.map e.toMonoidHom).subtype.comp ψ.toMonoidHom) :=
          Subgroup.map_map _ _ _
    _ = (Work.GW2.oddCore ↥K).map (e.toMonoidHom.comp K.subtype) := by rw [hcomp]
    _ = ((Work.GW2.oddCore ↥K).map K.subtype).map e.toMonoidHom :=
          (Subgroup.map_map _ _ _).symm
    _ = (Work.GW2.oddCoreIn K).map e.toMonoidHom := rfl

theorem oddCoreIn_card_map_mulAut {G : Type} [Group G] [Finite G] (e : MulAut G) (K : Subgroup G) :
    Nat.card (Work.GW2.oddCoreIn (K.map e.toMonoidHom)) =
      Nat.card (Work.GW2.oddCoreIn K) := by
  rw [oddCoreIn_eq_map_mulAut e K]
  exact Subgroup.card_map_of_injective (K := Work.GW2.oddCoreIn K) e.injective

end Work.CORE2B
