import Mathlib
import Submission.Work.ASM.Defs

/-!
# Odd-order subgroups live in `O_{2'}` when the complement is a 2-group

If `U = O_{2'}(H)` (the largest normal subgroup of `H` of odd order, transported into `G`) and
`H = U ⊔ S` with `S` a `2`-group, then `H/U ≅ S/(S ⊓ U)` is a `2`-group: it is a quotient of `S`.
Hence every odd-order subgroup `X ≤ H` must already lie in `U`, since its image in `H/U` has order
dividing both the odd number `|X|` and a power of `2`.

The proof is carried out in the abstract group `↥H`, where `U.subgroupOf H` is *normal* (it is
`O_{2'}(↥H)`, so the `Normal` instance for `Work.GW2.oddCore` applies). The general statement is
recorded as `le_of_sup_isPGroup` and then transported through `Subgroup.subgroupOf` to the ambient
group `G`.
-/

namespace Work.CORE2A

/-- If `U` is a normal subgroup of a finite group `G` with `U ⊔ S = ⊤` for a `2`-group `S`, then
`G ⧸ U` is a `2`-group, so every subgroup `X` of odd order lies in `U`.

Concretely `U.index = U.relIndex S ∣ |S| = 2 ^ n` and `U.relIndex X ∣ |X|` is odd; the relative
index `U.relIndex X`, dividing both a power of two and an odd number, equals `1`, i.e. `X ≤ U`. -/
theorem le_of_sup_isPGroup {G : Type*} [Group G] [Finite G] {U S X : Subgroup G}
    [U.Normal] (hUS : U ⊔ S = ⊤) (hS : IsPGroup 2 S) (hX : Odd (Nat.card X)) :
    X ≤ U := by
  -- `U` is normal, so its relative index in `X` divides its index in `G`.
  have h1 : U.relIndex X ∣ U.index := Subgroup.relIndex_dvd_index_of_normal U X
  -- `⊤ = U ⊔ S` makes `U.index` the index of `U ⊓ S` in `S`, hence a divisor of `|S|`.
  have hidx : U.index = U.relIndex S := by
    rw [← Subgroup.relIndex_top_right, ← hUS, Subgroup.relIndex_sup_left]
  have h2 : U.relIndex X ∣ U.relIndex S := hidx ▸ h1
  have h3 : U.relIndex X ∣ Nat.card S := h2.trans (Subgroup.relIndex_dvd_card U S)
  -- `U.relIndex X` also divides `|X|`.
  have h4 : U.relIndex X ∣ Nat.card X := Subgroup.relIndex_dvd_card U X
  -- `S` is a `2`-group, so `|S| = 2 ^ n`.
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hS
  have h5 : U.relIndex X ∣ 2 ^ n := hn ▸ h3
  -- `2 ^ n` and the odd number `|X|` are coprime, so `U.relIndex X = 1`, i.e. `X ≤ U`.
  have hnot : ¬ 2 ∣ Nat.card X := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hX
  have hcop : Nat.Coprime (2 ^ n) (Nat.card X) :=
    (Nat.prime_two.coprime_pow_of_not_dvd (m := n) hnot).symm
  have hone : U.relIndex X = 1 := Nat.eq_one_of_dvd_coprimes hcop h5 h4
  exact Subgroup.relIndex_eq_one.mp hone

theorem odd_subgroup_le_oddCoreIn {G : Type} [Group G] [Finite G] (H U S : Subgroup G)
    (hU : U = Work.GW2.oddCoreIn H) (hUS : U ⊔ S = H) (hS : IsPGroup 2 S) :
    ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → X ≤ U := by
  intro X hXH hXodd
  -- `U ≤ H` (as the image of `O_{2'}(H)` under `H.subtype`) and `S ≤ H`.
  have hUle : U ≤ H := hU ▸ Subgroup.map_subtype_le (Work.GW2.oddCore ↥H)
  have hSle : S ≤ H := hUS ▸ le_sup_right
  -- Work inside `↥H`, where `U.subgroupOf H = O_{2'}(↥H)` is normal.
  have hU'eq : U.subgroupOf H = Work.GW2.oddCore ↥H := by
    rw [hU, Work.GW2.oddCoreIn, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hUnorm : (U.subgroupOf H).Normal := hU'eq ▸ Work.GW2.oddCore_normal ↥H
  have hUS' : U.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUle hSle, hUS, Subgroup.subgroupOf_self]
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.comap_subtype
  have hXcard : Nat.card (X.subgroupOf H) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have hXodd' : Odd (Nat.card (X.subgroupOf H)) := hXcard.symm ▸ hXodd
  have hX' : X.subgroupOf H ≤ U.subgroupOf H :=
    @le_of_sup_isPGroup ↥H _ _ (U.subgroupOf H) (S.subgroupOf H) (X.subgroupOf H)
      hUnorm hUS' hS' hXodd'
  intro x hx
  have hmem : (⟨x, hXH hx⟩ : ↥H) ∈ X.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hX' hmem)

end Work.CORE2A
