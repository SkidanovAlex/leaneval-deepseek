import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- For subgroups `H` and a normal subgroup `K` of a group, the order of `H ⊔ K` divides
the product of the orders of `H` and `K`.  This is the numerical content of the isomorphism
`(H ⊔ K)/K ≅ H/(H ⊓ K)`: indeed `Nat.card ↥(H ⊔ K) = [K : (H ⊓ K)] * Nat.card ↥K`
and `[K : (H ⊓ K)] = (K.subgroupOf H).index ∣ Nat.card ↥H`. -/
theorem card_sup_dvd_mul_card_of_normal {G : Type*} [Group G] {H K : Subgroup G} [K.Normal] :
    Nat.card ↥(H ⊔ K) ∣ Nat.card ↥H * Nat.card ↥K := by
  have hcard : Nat.card ↥(K.subgroupOf (H ⊔ K)) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : K ≤ H ⊔ K)).toEquiv
  have hmul : K.relIndex (H ⊔ K) * Nat.card ↥(K.subgroupOf (H ⊔ K)) = Nat.card ↥(H ⊔ K) :=
    Subgroup.index_mul_card (K.subgroupOf (H ⊔ K))
  have hsup : Nat.card ↥(H ⊔ K) = (K.subgroupOf H).index * Nat.card ↥K := by
    rw [← hmul, Subgroup.relIndex_sup_right, hcard]
    rfl
  obtain ⟨d, hd⟩ := Subgroup.index_dvd_card (K.subgroupOf H)
  refine ⟨d, ?_⟩
  rw [hsup, hd]
  ring

/-- The supremum of two normal `π`-subgroups is a normal `π`-subgroup. -/
theorem piCoreSet_sup_mem {G : Type*} [Group G] {π : ℕ → Prop} {N M : Subgroup G}
    (hN : N ∈ piCoreSet π G) (hM : M ∈ piCoreSet π G) : N ⊔ M ∈ piCoreSet π G := by
  rw [mem_piCoreSet] at hN hM ⊢
  haveI : N.Normal := hN.1
  haveI : M.Normal := hM.1
  exact ⟨Subgroup.sup_normal N M,
    isPiNat_of_dvd (card_sup_dvd_mul_card_of_normal (H := N) (K := M))
      (IsPiNat.mul hN.2 hM.2)⟩

theorem mem_piCore_iff {G : Type*} [Group G] [Finite G] {π : ℕ → Prop} {x : G} :
    x ∈ Work.Fitting.piCore π G ↔ ∃ N ∈ Work.Fitting.piCoreSet π G, x ∈ N := by
  have hne : (piCoreSet π G).Nonempty :=
    ⟨⊥, Subgroup.normal_bot, by rw [Subgroup.card_bot]; exact isPiNat_one π⟩
  have hdir : DirectedOn (· ≤ ·) (piCoreSet π G) := by
    intro N hN M hM
    exact ⟨N ⊔ M, piCoreSet_sup_mem hN hM, le_sup_left, le_sup_right⟩
  rw [piCore, Subgroup.mem_sSup_of_directedOn hne hdir]

end Work.Fitting
