import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

/-- **Structure lemma.** If a subgroup `T` normalises a subgroup `K` (i.e. `T ≤ N_G(K)`), then
Noether's second isomorphism theorem gives
`(K ⊔ T)/K ≅ T/(T ⊓ K)`, whence `|K ⊔ T| = |K| * |(K ⊔ T) : K|` with `|(K ⊔ T) : K|` dividing
`|T|`. -/
theorem card_sup_dvd_mul_card_of_le_normalizer {G : Type} [Group G] {K T : Subgroup G}
    (hle : T ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(K ⊔ T) ∣ Nat.card ↥K * Nat.card ↥T := by
  have : (K.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hle
  have : (K.subgroupOf (T ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
  -- the index of `K` in `T ⊔ K` equals its index in `T`
  have hindex : (K.subgroupOf (T ⊔ K)).index = (K.subgroupOf T).index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T K hle).toEquiv.symm
  have hdvd : (K.subgroupOf T).index ∣ Nat.card ↥T := Subgroup.index_dvd_card _
  -- `|K ⊔ T| = |K| * [K ⊔ T : K]`
  have hcard : Nat.card ↥(K ⊔ T) = Nat.card ↥K * (K.subgroupOf (T ⊔ K)).index := by
    rw [sup_comm, ← Subgroup.card_mul_index (K.subgroupOf (T ⊔ K))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv
  rw [hcard]
  exact Nat.mul_dvd_mul_left _ (hindex.symm ▸ hdvd)

/-- If an involution `s` normalises a subgroup `K ≤ G`, then `|K ⊔ ⟨s⟩|` divides `2 * |K|`
(the join is the set product `K * ⟨s⟩`, of cardinality `|K| * |⟨s⟩| / |K ⊓ ⟨s⟩`). -/
theorem card_sup_zpowers_dvd {G : Type} [Group G] [Finite G] {K : Subgroup G} {s : G}
    (hs : orderOf s = 2) (hKs : Submission.Blueprint.conj s K = K) :
    Nat.card ↥(K ⊔ Subgroup.zpowers s) ∣ 2 * Nat.card ↥K := by
  have hmem : s ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [Submission.Blueprint.conj] using hKs
  have hle : Subgroup.zpowers s ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hmem
  have h := card_sup_dvd_mul_card_of_le_normalizer (K := K) hle
  rw [Nat.card_zpowers, hs] at h
  rwa [mul_comm 2 (Nat.card ↥K)]

end Work.ThreePoints.ThmC
