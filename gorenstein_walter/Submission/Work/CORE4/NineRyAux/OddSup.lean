import Mathlib

/-!
# Odd-order subgroups and `2`-group quotients

Two auxiliary facts used to show that a subgroup of odd order contained in
`U ⊔ S`, with `S` a `2`-group and `U` normal in `U ⊔ S`, must already lie in `U`.

* `isPGroup_quotient_sup_of_normal`: if `S` is a `p`-group and `U` is normal in
  `U ⊔ S`, then the quotient `(U ⊔ S) / U` is a `p`-group.  This is the second
  isomorphism theorem: `(U ⊔ S)/U ≅ S/(S ∩ U)`.
* `le_of_isPGroup_quotient_of_not_dvd_card`: if `N` is normal in `G`, the quotient
  `G / N` is a `p`-group and `p ∤ |K|` for a subgroup `K ≤ G`, then `K ≤ N`.
-/

namespace Work.CORE4.NineRyAux

/-- The quotient of `U ⊔ S` by `U` is a `p`-group whenever `S` is a `p`-group and
`U` is normal in `U ⊔ S`.  (Second isomorphism theorem.) -/
theorem isPGroup_quotient_sup_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ}
    {U S : Subgroup G} (hU : (U.subgroupOf (U ⊔ S)).Normal) (hS : IsPGroup p S) :
    IsPGroup p (↥(U ⊔ S) ⧸ U.subgroupOf (U ⊔ S)) := by
  have hN : (U.subgroupOf (U ⊔ S)).Normal := hU
  obtain ⟨k, hk⟩ := (isPGroup_iff_card_dvd_pow (p := p) (G := ↥S)).mp hS
  refine IsPGroup.of_card_dvd_pow (n := k) ?_
  rw [← Subgroup.index_eq_card (U.subgroupOf (U ⊔ S))]
  have hsup : (⊤ : Subgroup ↥(U ⊔ S))
      = S.subgroupOf (U ⊔ S) ⊔ U.subgroupOf (U ⊔ S) := by
    rw [← Subgroup.subgroupOf_self (U ⊔ S), Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact sup_comm _ _
  have hindex : (U.subgroupOf (U ⊔ S)).index
      = (U.subgroupOf (U ⊔ S)).relIndex (S.subgroupOf (U ⊔ S)) := by
    rw [← Subgroup.relIndex_top_right (H := U.subgroupOf (U ⊔ S)), hsup]
    exact Subgroup.relIndex_sup_right (H := S.subgroupOf (U ⊔ S))
      (K := U.subgroupOf (U ⊔ S))
  rw [hindex]
  calc (U.subgroupOf (U ⊔ S)).relIndex (S.subgroupOf (U ⊔ S))
      ∣ Nat.card ↥(S.subgroupOf (U ⊔ S)) :=
        Subgroup.relIndex_dvd_card (H := U.subgroupOf (U ⊔ S))
          (K := S.subgroupOf (U ⊔ S))
    _ = Nat.card ↥S :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ U ⊔ S)).toEquiv
    _ ∣ p ^ k := hk

/-- If `N ◁ G`, `G ⧸ N` is a `p`-group and `p ∤ |K|`, then `K ≤ N`.
Indeed the image of `K` in `G ⧸ N` is a quotient of `K` (so its order divides `|K|`)
and a subgroup of a `p`-group (so its order is a power of `p`); it is therefore trivial. -/
theorem le_of_isPGroup_quotient_of_not_dvd_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {N K : Subgroup G} [N.Normal]
    (hq : IsPGroup p (G ⧸ N)) (hK : ¬ p ∣ Nat.card K) : K ≤ N := by
  let φ : G →* G ⧸ N := QuotientGroup.mk' N
  let κ : K →* G ⧸ N := φ.comp K.subtype
  have hran : κ.range = K.map φ := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, x.2, hx⟩
    · rintro ⟨x, hxK, hxy⟩
      exact ⟨⟨x, hxK⟩, hxy⟩
  have hdvd : Nat.card ↥(K.map φ) ∣ Nat.card ↥K := by
    have heq : Nat.card ↥(K.map φ) = Nat.card (K ⧸ κ.ker) := by
      rw [← hran]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange κ).toEquiv).symm
    rw [heq]
    exact Subgroup.card_quotient_dvd_card κ.ker
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥(K.map φ))).mp
    (IsPGroup.to_subgroup (G := G ⧸ N) hq (K.map φ))
  have hn0 : n = 0 := by
    by_contra h
    exact hK (dvd_pow_self p h |>.trans (hn ▸ hdvd))
  have h1 : K.map φ = ⊥ :=
    Subgroup.card_eq_one.mp (by rw [hn, hn0, pow_zero])
  rwa [Subgroup.map_eq_bot_iff K, QuotientGroup.ker_mk'] at h1

/-- A subgroup of odd order contained in `U ⊔ S`, where `S` is a `2`-group and `U` is
normal in `U ⊔ S`, lies in `U`. -/
theorem OddSup {G : Type*} [Group G] [Finite G]
    {U S X : Subgroup G} (hU : (U.subgroupOf (U ⊔ S)).Normal) (hS : IsPGroup 2 S)
    (hX : X ≤ U ⊔ S) (hodd : Odd (Nat.card X)) : X ≤ U := by
  have hq : IsPGroup 2 (↥(U ⊔ S) ⧸ U.subgroupOf (U ⊔ S)) :=
    isPGroup_quotient_sup_of_normal hU hS
  have hU' : (U.subgroupOf (U ⊔ S)).Normal := hU
  have hK : ¬ 2 ∣ Nat.card ↥(X.subgroupOf (U ⊔ S)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  have hmain : X.subgroupOf (U ⊔ S) ≤ U.subgroupOf (U ⊔ S) :=
    le_of_isPGroup_quotient_of_not_dvd_card hq hK
  intro x hx
  have hx' : (⟨x, hX hx⟩ : ↥(U ⊔ S)) ∈ X.subgroupOf (U ⊔ S) := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have h2 := hmain hx'
  rwa [Subgroup.mem_subgroupOf] at h2

end Work.CORE4.NineRyAux
