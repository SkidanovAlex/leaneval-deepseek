import Mathlib
import Submission.Work.GroupTheory.conj_mul_centralizer_of_sup_zpowers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.exists_conj_commuting_mul`

Let `K` be a normal Hall subgroup of a finite group `G` with complement `M` (`K ⊔ M = ⊤`,
`K ⊓ M = ⊥`, coprime orders).  Then every element `g ∈ G` is conjugate to a product `k * m` with
`k ∈ K`, `m ∈ M` and `k * m = m * k`.

Write `g = k * m`.  The element `g` lives in the subgroup `H = K ⊔ ⟨m⟩`, in which `K` is still a
normal Hall subgroup with cyclic quotient `H/K ≅ ⟨m⟩`.  Wielandt's product lemma
(`Work.GroupTheory.conj_mul_centralizer_of_sup_zpowers`) applied inside `H` conjugates `k * m` to
`k' * m` with `k' ∈ K` commuting with `m`.
-/

namespace Work.Tame

theorem exists_conj_commuting_mul {G : Type*} [Group G] [Fintype G] (K M : Subgroup G) [K.Normal]
    (hsup : K ⊔ M = ⊤) (hinf : K ⊓ M = ⊥) (hcop : (Nat.card K).Coprime (Nat.card M)) (g : G) :
    ∃ z : G, ∃ k ∈ K, ∃ m ∈ M, k * m = m * k ∧ z * g * z⁻¹ = k * m := by
  classical
  -- decompose `g = k * m` using `K ⊔ M = ⊤` (`K` normal)
  obtain ⟨k, hk, m, hm, hkm⟩ :=
    Subgroup.mem_sup_of_normal_left.mp
      (show g ∈ K ⊔ M by rw [hsup]; exact Subgroup.mem_top g)
  -- work inside `H = K ⊔ ⟨m⟩`
  let H : Subgroup G := K ⊔ Subgroup.zpowers m
  have hKH : K ≤ H := le_sup_left
  have hzpH : Subgroup.zpowers m ≤ H := le_sup_right
  have hmH : m ∈ H := hzpH (Subgroup.mem_zpowers m)
  have hkH : k ∈ H := hKH hk
  -- coprimality hypotheses for the product lemma
  have hcopm : (Nat.card K).Coprime (orderOf m) :=
    hcop.coprime_dvd_right (Subgroup.orderOf_dvd_natCard M hm)
  have hcopH : (Nat.card ↥(K.subgroupOf H)).Coprime (orderOf (⟨m, hmH⟩ : ↥H)) := by
    have hcard : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
    rw [hcard, Subgroup.orderOf_mk m hmH]
    exact hcopm
  -- `K.subgroupOf H` and `⟨m⟩` are complementary in `H`
  have htopH : K.subgroupOf H ⊔ Subgroup.zpowers (⟨m, hmH⟩ : ↥H) = ⊤ := by
    have hzp : Subgroup.zpowers (⟨m, hmH⟩ : ↥H) = (Subgroup.zpowers m).subgroupOf H := by
      ext y
      rw [Subgroup.mem_zpowers_iff, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, by rw [Subgroup.coe_zpow]⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa [Subgroup.coe_zpow] using hn)⟩
    rw [hzp, ← Subgroup.subgroupOf_sup hKH hzpH]
    exact Subgroup.subgroupOf_self H
  haveI : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf
  -- Wielandt's product lemma inside `H`
  obtain ⟨a', z, hcomm, hconj⟩ :=
    Work.GroupTheory.conj_mul_centralizer_of_sup_zpowers (G := ↥H)
      (A := K.subgroupOf H) (b := (⟨m, hmH⟩ : ↥H)) hcopH htopH
      (⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk⟩ : ↥(K.subgroupOf H))
  refine ⟨(z : G), ((a' : ↥H) : G), ?_, m, hm, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp a'.2
  · simpa using congrArg (Subtype.val : ↥H → G) hcomm
  · rw [← hkm]
    simpa using congrArg (Subtype.val : ↥H → G) hconj

end Work.Tame
