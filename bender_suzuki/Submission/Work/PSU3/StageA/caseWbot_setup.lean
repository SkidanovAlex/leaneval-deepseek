/-
# `Work.PSU3.StageA.caseWbot_setup` — setup lemmas for the `W = ⊥` branch of Stage A

The lemmas collected here are the ones that the nodes of the `caseWbot` family
(`caseWbot_nonabelian_card_order` and its siblings) share: Ch. V §1 Prop. 2 with
`FeitThompsonProp` (`K = J(D,t)` cyclic), the Suzuki structure of `Q`, Higman's cardinality
dichotomy `|Q| = q²` or `q³`, and the existence of a prime-order subgroup of `V = centD H t`.

They are kept in their own module so that the `caseWbot` nodes can import them **without**
importing each other (the main module imports the nodes).
-/
import Mathlib
import Submission.Work.PSU3.StageA.lemma2cHig
import Submission.Work.PSU3.BenderST.benderSTProp_holds
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.Higman.Main
import Submission.Work.ThmF.ChV12.corProp2
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.PSU3.StageA.twoPoint_eq_Kset_mul_centD
import Submission.Work.PSU3.StageA.W_centralizes_Q0sub
import Submission.Work.ThmF.ChV12.lemma4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-!
## Setup for the `W = ⊥` branch with `Q` non-abelian

Peterfalvi II, Ch. V §1 Prop. 2 with the odd order theorem (`FeitThompsonProp`) gives that
`K = J(D,t)` is a cyclic normal subgroup of `D = twoPoint H t`; consequently `Q` is a Suzuki
`2`-group (Ch. V §1 Corollary of Prop. 2), and Higman's Theorem 1 (`Work.Higman.higmanProp`)
gives `|Q| = q²` or `q³` for `q = |Z(Q)| = |Q0sub H|`.
-/

/-- **Ch. V §1 Prop. 2 with `FeitThompsonProp`**: `K = J(D,t)` is cyclic, equal to the set
`Kset H t`, and normal in `D = twoPoint H t`. -/
theorem caseWbot_K_facts (hS : Work.PSU3.PSU3Hyp H Q t) (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    IsCyclic ↥(Work.ThmF.Ksub H t) ∧ (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t ∧
      ((Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal :=
  Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS.situation hS.split

/-- **Ch. V §1 Corollary of Prop. 2 (`W = ⊥` branch, `Q` non-abelian)**: `Q` is a Suzuki
`2`-group.  The conjugating group is `K = Ksub H t = Kset H t`, cyclic by `caseWbot_K_facts`,
acting regularly on `Inv H = Z(Q)♯`. -/
theorem caseWbot_isSuzukiTwoGroup (hS : Work.PSU3.PSU3Hyp H Q t)
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q) :
    Submission.Blueprint.IsSuzukiTwoGroup ↥Q := by
  obtain ⟨hcyc, hKset, -⟩ := caseWbot_K_facts hS hFT hC4
  have hStab : ∀ k ∈ Work.ThmF.Ksub H t, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := by
    intro k hk x hx
    have hkH : k ∈ H := Work.ThmF.ChV12.Ksub_le_H H t hk
    exact (Subgroup.mem_normalizer_iff.mp (hS.split.normal hkH) x).mp hx
  have hcard : 2 ≤ (Submission.Blueprint.involutions (Q : Set G)).ncard := by
    have h1 : 2 ≤ (Submission.Blueprint.involutions (H : Set G)).ncard :=
      Work.ThmF.Bender.cardInvGeTwo hS.split.stronglyEmbedded hS.situation.1.1
    exact le_trans h1 (Set.ncard_le_ncard
      (fun u hu => ⟨caseC_involutions_subset_Q hS.split hu, hu.2⟩) (Set.toFinite _))
  have htrans : ∀ a ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ b ∈ Submission.Blueprint.involutions (H : Set G),
      ∃ k ∈ Work.ThmF.Kset H t, k * a * k⁻¹ = b := by
    intro a ha b hb
    obtain ⟨k, hk, -⟩ := Work.ThmF.L5.Kset_regular hS.split a ha b hb
    exact ⟨k, hk.1, hk.2⟩
  exact Work.ThmF.ChV12.isSuzukiTwoGroup_of_Ksub_cyclic H t Q hS.split.le hS.two hStab hcard hnab
    hcyc hKset htrans

/-- In a Suzuki `2`-group the centre is the set of elements of order `≤ 2`, so the centre of `Q`
is `Q0sub H` (via `caseC_Q0sub_subgroupOf_iff_sq`). -/
theorem caseWbot_center_subgroupOf (hS : Work.PSU3.PSU3Hyp H Q t)
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q) :
    Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q := by
  have hSuz := caseWbot_isSuzukiTwoGroup hS hFT hC4 hnab
  have hcenter := (Work.Higman.higmanProp ↥Q hSuz).1
  ext x
  rw [Subgroup.mem_subgroupOf]
  exact (hcenter x).trans ((by rw [pow_two] :
    x ^ 2 = 1 ↔ x * x = 1).trans (caseC_Q0sub_subgroupOf_iff_sq hS hC4 x).symm)

/-- **Higman's dichotomy**: `|Q| = q²` or `q³` with `q = |Q0sub H|`. -/
theorem caseWbot_card_dichotomy (hS : Work.PSU3.PSU3Hyp H Q t)
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q) :
    Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 2 ∨
      Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3 := by
  have hSuz := caseWbot_isSuzukiTwoGroup hS hFT hC4 hnab
  have hdich := (Work.Higman.higmanProp ↥Q hSuz).2.2.2.1
  have hc : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [caseWbot_center_subgroupOf hS hFT hC4 hnab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Work.PSU3.StageA.Q0sub_le_Q hS.split)).toEquiv
  rwa [hc] at hdich

/-- `Q0sub H` has `2`-power order: it is an elementary abelian `2`-group
(`Work.ThmF.ChV12.Q0sub_elementary`). -/
theorem caseWbot_Q0sub_card_pow_two (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∃ n : ℕ, Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := by
  have hcomm : ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u :=
    Work.ThmF.ChV12.involutions_of_H_commute hS.situation hC4 H Q t hS.split
  have hsq := (Work.ThmF.ChV12.Q0sub_elementary H hcomm).1
  have hp : IsPGroup 2 ↥(Work.ThmF.Q0sub H) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq (x : G) x.2)⟩
  exact IsPGroup.iff_card.mp hp

/-- A subgroup of `V = centD H t` of prime order exists (`V ≠ ⊥`). -/
theorem caseWbot_exists_prime_subgroup_centD (hS : Work.PSU3.PSU3Hyp H Q t) :
    ∃ P : Subgroup G, P ≤ Submission.Blueprint.centD H t ∧ (Nat.card P).Prime := by
  have hV : Submission.Blueprint.centD H t ≠ ⊥ := Work.PSU3.StageA.centD_ne_bot hS
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ Submission.Blueprint.centD H t, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hV (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)))
  have hord1 : orderOf v ≠ 1 := fun h => hv1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
  have hpcard : p ∣ Nat.card ↥(Submission.Blueprint.centD H t) :=
    hpdvd.trans (Subgroup.orderOf_dvd_natCard _ hv)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Submission.Blueprint.centD H t))
    p hpcard
  refine ⟨Subgroup.zpowers ((x : ↥(Submission.Blueprint.centD H t)) : G), ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn]
    exact (Submission.Blueprint.centD H t).zpow_mem x.2 _
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    exact hp

end Work.PSU3.StageA
