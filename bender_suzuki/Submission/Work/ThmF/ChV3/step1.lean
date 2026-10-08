import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV12.prop3_quot_cyclic
import Submission.Work.ThmF.ChV12.lemma2a
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV12.KsubSubgroupOfNormal
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmF.Bender.cardKsetEqInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary facts from `ChIIFourProp` and `(F1)`

Everything in this section is proved from `Situation G`, `ChIIFourProp`,
`IsSplitRankOne H Q t` and the hypothesis

**(F1)** there is `P ≤ V = centD H t` of prime order with `¬ HasFourGroup (C_G(P))`

alone (no `FeitThompsonProp`, no `Ksub H t = Kset H t`). -/

/-- Ch. II §4 Prop. 4: `W = C_V(K) = C_D(Inv H)`. -/
theorem W_eq_inf_centralizer_involutions {H Q : Subgroup G} {t : G} (hS : Situation G)
    (hC4 : ChIIFourProp) (h : IsSplitRankOne H Q t) :
    Work.ThmF.W H t = twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) := by
  have hP4 := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.2.2.2.1
  simpa only [Work.ThmF.W, Work.ThmF.Kset] using hP4

/-- Conjugation by an element of `V = C_D(t)` preserves `K = J(D,t)`. -/
theorem conj_mem_Kset_of_mem_centD {H : Subgroup G} {t x : G} (hx : x ∈ centD H t) {k : G}
    (hk : k ∈ Work.ThmF.Kset H t) : x * k * x⁻¹ ∈ Work.ThmF.Kset H t := by
  obtain ⟨hkD, hkinv⟩ := Work.ThmF.mem_Kset_iff.mp hk
  have hxD : x ∈ twoPoint H t := (Subgroup.mem_inf.mp hx).1
  have hxt : t * x * t⁻¹ = x := by
    have h1 : x * t = t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    rw [← h1]; group
  refine Work.ThmF.mem_Kset_iff.mpr ⟨?_, ?_⟩
  · exact (twoPoint H t).mul_mem ((twoPoint H t).mul_mem hxD hkD) ((twoPoint H t).inv_mem hxD)
  · calc t * (x * k * x⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * k * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
      _ = x * k⁻¹ * x⁻¹ := by rw [hxt, hkinv]
      _ = (x * k * x⁻¹)⁻¹ := by group

/-- The map `k ↦ k u k⁻¹ : K → Inv H` is injective (Ch. I §2: `K` acts regularly on `Inv H`). -/
theorem Kset_conj_injective {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) {u : G}
    (hu : u ∈ involutions (H : Set G)) {k k' : G} (hk : k ∈ Work.ThmF.Kset H t)
    (hk' : k' ∈ Work.ThmF.Kset H t) (heq : k * u * k⁻¹ = k' * u * k'⁻¹) : k = k' := by
  have hkH : k ∈ H := (Subgroup.mem_inf.mp (Work.ThmF.Kset_le_twoPoint (H := H) t hk)).1
  have hmem : k * u * k⁻¹ ∈ involutions (H : Set G) :=
    ⟨H.mul_mem (H.mul_mem hkH hu.1) (H.inv_mem hkH), by rw [Bender.orderOf_conj_eq, hu.2]⟩
  obtain ⟨k₀, _hk₀, huniq⟩ := Work.ThmF.L5.Kset_regular h u hu (k * u * k⁻¹) hmem
  rw [huniq k ⟨hk, rfl⟩, huniq k' ⟨hk', heq.symm⟩]

/-- Two distinct commuting involutions of `H` centralised by `P` give a four-group in `C_G(P)`. -/
theorem hasFourGroup_centralizer_of_two_involutions {H : Subgroup G} {P : Subgroup G} {u v : G}
    (hu : u ∈ involutions (H : Set G)) (hv : v ∈ involutions (H : Set G)) (huv : u ≠ v)
    (hcomm : u * v = v * u) (huP : u ∈ Subgroup.centralizer (P : Set G))
    (hvP : v ∈ Subgroup.centralizer (P : Set G)) :
    HasFourGroup ↥(Subgroup.centralizer (P : Set G)) :=
  ⟨⟨u, huP⟩, ⟨v, hvP⟩, by rw [← Subgroup.orderOf_coe]; exact hu.2,
    by rw [← Subgroup.orderOf_coe]; exact hv.2, fun h => huv (congrArg Subtype.val h),
    Subtype.ext hcomm⟩

/-- **Step (1), first clause.** `W ∩ P = 1`: by `ChIIFourProp` (Prop. 4) `W = C_D(Inv H)`, so
`P ≤ W` would make every involution of `H` centralise `P`, producing a four-group in `C_G(P)`. -/
theorem W_inf_eq_bot_of_prime {H Q : Subgroup G} {t : G} (hS : Situation G) (hC4 : ChIIFourProp)
    (h : IsSplitRankOne H Q t) {P : Subgroup G} (hPprime : (Nat.card P).Prime)
    (hF1 : ¬ HasFourGroup ↥(Subgroup.centralizer (P : Set G))) :
    Work.ThmF.W H t ⊓ P = ⊥ := by
  classical
  have hcomm := L5.involutions_commute hS hC4 h
  have hW := W_eq_inf_centralizer_involutions hS hC4 h
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxW, hxP⟩ := Subgroup.mem_inf.mp hx
  -- `⟨x⟩ = P`, hence `P ≤ W`
  have hzle : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.mpr hxP
  have hdvd : orderOf x ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hxP
  have hne : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
  have hord : orderOf x = Nat.card P := by
    rcases hPprime.eq_one_or_self_of_dvd (orderOf x) hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hcard : Nat.card ↥(Subgroup.zpowers x) = Nat.card P := by
    rw [Nat.card_zpowers, hord]
  have hEq : Subgroup.zpowers x = P :=
    Subgroup.eq_of_le_of_card_ge hzle (le_of_eq hcard.symm)
  have hPW : P ≤ Work.ThmF.W H t := fun y hy =>
    Subgroup.zpowers_le.mpr hxW (by rw [hEq]; exact hy)
  -- every involution of `H` centralises `P`
  have hcent : ∀ u ∈ involutions (H : Set G), u ∈ Subgroup.centralizer (P : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpC : p ∈ Subgroup.centralizer (involutions (H : Set G)) := by
      have hpW : p ∈ Work.ThmF.W H t := hPW hp
      rw [hW] at hpW
      exact (Subgroup.mem_inf.mp hpW).2
    exact (Subgroup.mem_centralizer_iff.mp hpC u hu).symm
  -- two distinct involutions of `H`
  have h2 : 2 ≤ (involutions (H : Set G)).ncard :=
    Bender.cardInvGeTwo h.stronglyEmbedded hS.1.1
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (Set.one_lt_ncard (s := involutions (H : Set G))).mp
      (show 1 < (involutions (H : Set G)).ncard by omega)
  exact hF1 (hasFourGroup_centralizer_of_two_involutions hu hv huv (hcomm u hu v hv)
    (hcent u hu) (hcent v hv))

/-- The involution `u ∈ Inv H` of Ch. II §4 Prop. 2 (a) (the one with `V = C_D(u)`) is
centralised by `P ≤ V`. -/
theorem exists_involution_centralizing_P {H Q : Subgroup G} {t : G} (hS : Situation G)
    (hC4 : ChIIFourProp) (h : IsSplitRankOne H Q t) {P : Subgroup G} (hPV : P ≤ centD H t) :
    ∃ u ∈ involutions (H : Set G), u ∈ Subgroup.centralizer (P : Set G) := by
  obtain ⟨u, hu, huV⟩ := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.1
  refine ⟨u, hu, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hpV : p ∈ twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) := by
    rw [← huV]; exact hPV hp
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hpV).2

/-- **Step (1): `|C_{Q₀}(P)| = 2`.**  `C_{Q₀}(P)` is an elementary abelian `2`-subgroup of
`C_G(P)`, hence has no four-group (it has order `≤ 2`), and it contains the involution `u` of
Ch. II §4 Prop. 2 (a). -/
theorem Q0sub_inf_centralizer_card {H Q : Subgroup G} {t : G} (hS : Situation G)
    (hC4 : ChIIFourProp) (h : IsSplitRankOne H Q t) {P : Subgroup G} (hPV : P ≤ centD H t)
    (hF1 : ¬ HasFourGroup ↥(Subgroup.centralizer (P : Set G))) :
    Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) = 2 := by
  classical
  have hcomm := L5.involutions_commute hS hC4 h
  have hQ0elem := L5.Q0sub_elementary (H := H) hcomm
  obtain ⟨u, hu, huC⟩ := exists_involution_centralizing_P hS hC4 h hPV
  have huQ : u ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hu)
  have huT : u ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_inf.mpr ⟨huQ, huC⟩
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 := hu.2
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  -- `C_{Q₀}(P) ≤ {1, u}`
  have hsub : ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G)
      ⊆ ({1, u} : Set G) := by
    intro x hx
    by_contra hxc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxc
    obtain ⟨hx1, hxu⟩ := hxc
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxinv : x ∈ involutions (H : Set G) := hQ0elem.2.2 x hxQ hx1
    exact hF1 (hasFourGroup_centralizer_of_two_involutions hxinv hu hxu
      (hcomm x hxinv u hu) hxC huC)
  have hcard_le : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) ≤ 2 := by
    calc Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))
        = ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ ({1, u} : Set G).ncard := Set.ncard_le_ncard hsub
      _ = 2 := Set.ncard_pair (Ne.symm hu1)
  have hcard_ge : 2 ≤ Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := by
    have hpair : ({1, u} : Set G)
        ⊆ ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact huT
    have hcard : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))
        = ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G).ncard :=
      Nat.card_coe_set_eq _
    rw [hcard]
    have h1 : 2 ≤ ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :
        Set G).ncard := by
      calc (2 : ℕ) = ({1, u} : Set G).ncard := (Set.ncard_pair (Ne.symm hu1)).symm
        _ ≤ _ := Set.ncard_le_ncard hpair
    omega
  omega

/-- **Step (1): `C_K(P) = 1`.**  If `k ∈ K ∖ {1}` centralised `P`, then `k u k⁻¹ ≠ u` would be a
second involution of `H` centralised by `P`, giving a four-group in `C_G(P)`. -/
theorem Kset_inf_centralizer_eq_bot {H Q : Subgroup G} {t : G} (hS : Situation G)
    (hC4 : ChIIFourProp) (h : IsSplitRankOne H Q t) {P : Subgroup G} (hPV : P ≤ centD H t)
    (hF1 : ¬ HasFourGroup ↥(Subgroup.centralizer (P : Set G))) :
    Work.ThmF.Kset H t ∩ (Subgroup.centralizer (P : Set G) : Set G) = {1} := by
  classical
  have hcomm := L5.involutions_commute hS hC4 h
  obtain ⟨u, hu, huC⟩ := exists_involution_centralizing_P hS hC4 h hPV
  refine Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨Work.ThmF.one_mem_Kset H t, Subgroup.one_mem _⟩, ?_⟩
  rintro x ⟨hkx, hxC⟩
  by_contra hx1
  have hxH : x ∈ H := (Subgroup.mem_inf.mp (Work.ThmF.Kset_le_twoPoint (H := H) t hkx)).1
  have hxinv : x * u * x⁻¹ ∈ involutions (H : Set G) :=
    ⟨H.mul_mem (H.mul_mem hxH hu.1) (H.inv_mem hxH), by rw [Bender.orderOf_conj_eq, hu.2]⟩
  have hne : x * u * x⁻¹ ≠ u := fun heq =>
    hx1 (Kset_conj_injective h hu hkx (Work.ThmF.one_mem_Kset H t)
      (by rw [heq]; group))
  have hcent : x * u * x⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpx : p * x = x * p := Subgroup.mem_centralizer_iff.mp hxC p hp
    have hpu : p * u = u * p := Subgroup.mem_centralizer_iff.mp huC p hp
    have hpxi : p * x⁻¹ = x⁻¹ * p := by
      have h2 : p * x * p⁻¹ = x := by rw [hpx]; group
      calc p * x⁻¹ = p * x⁻¹ * p⁻¹ * p := by group
        _ = (p * x * p⁻¹)⁻¹ * p := by rw [show p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ by group]
        _ = x⁻¹ * p := by rw [h2]
    calc p * (x * u * x⁻¹) = (p * x) * u * x⁻¹ := by group
      _ = (x * p) * u * x⁻¹ := by rw [hpx]
      _ = x * (p * u) * x⁻¹ := by group
      _ = x * (u * p) * x⁻¹ := by rw [hpu]
      _ = x * u * (p * x⁻¹) := by group
      _ = x * u * (x⁻¹ * p) := by rw [hpxi]
      _ = (x * u * x⁻¹) * p := by group
  exact hF1 (hasFourGroup_centralizer_of_two_involutions hxinv hu hne
    (hcomm (x * u * x⁻¹) hxinv u hu) hcent huC)

/-- **The reduction of the missing ingredient.**  `K = J(D,t)` is a subgroup as soon as its
elements commute pairwise: `t (k₁ k₂) t = (k₂ k₁)⁻¹`, so pairwise commutativity is exactly what
closes `Kset` under multiplication. -/
theorem Ksub_eq_Kset_of_pairwise_commute {H : Subgroup G} {t : G}
    (hcomm : ∀ k₁ ∈ Work.ThmF.Kset H t, ∀ k₂ ∈ Work.ThmF.Kset H t, k₁ * k₂ = k₂ * k₁) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  let Kgrp : Subgroup G :=
    { carrier := Work.ThmF.Kset H t
      one_mem' := Work.ThmF.one_mem_Kset H t
      mul_mem' := by
        intro a b ha hb
        have h1 := Work.ThmF.mem_Kset_iff.mp ha
        have h2 := Work.ThmF.mem_Kset_iff.mp hb
        refine Work.ThmF.mem_Kset_iff.mpr ⟨(twoPoint H t).mul_mem h1.1 h2.1, ?_⟩
        have h3 : t * (a * b) * t⁻¹ = a⁻¹ * b⁻¹ := by
          rw [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group, h1.2, h2.2]
        rw [h3, show a⁻¹ * b⁻¹ = (a * b)⁻¹ by rw [← mul_inv_rev, hcomm a ha b hb]]
      inv_mem' := by
        intro a ha
        have h1 := Work.ThmF.mem_Kset_iff.mp ha
        refine Work.ThmF.mem_Kset_iff.mpr ⟨(twoPoint H t).inv_mem h1.1, ?_⟩
        rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group, h1.2, inv_inv] }
  have hcarrier : (Work.ThmF.Kset H t : Set G) = (Kgrp : Set G) := rfl
  rw [Work.ThmF.Ksub, hcarrier, Subgroup.closure_eq]

/-! ## The target statement -/


end Work.ThmF.ChV3
