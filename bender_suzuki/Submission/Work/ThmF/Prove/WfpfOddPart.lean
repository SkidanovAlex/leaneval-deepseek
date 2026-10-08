import Mathlib
import Submission.Work.ThmF.ChV3.l2cCentralizerOddPart
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV12.exists_k_normalizing
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.DTransitiveInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.WfpfOddPart` — Ch. V §2 Lemma 2 (c) at `w ∈ W#`

In the standing context of §3 (`CtxF H Q t s r P`) with `Q` nilpotent and `|Q₀| = 2^{|P|}`, every
non-trivial element `w` of `W = C_V(K)` centralises no non-trivial element of `Q₁ = O_{2'}(Q)`:

  `O_{2'}(Q) ⊓ C_G(w) = ⊥`.

This is the fixed-point-freeness of `W` on `Q₁` needed by §3 step (9).  It is an instance of the
`C_{Q₁}(X) = 1` clause of Ch. II §4 Prop. 3 as packaged in
`Work.ThmF.ChV3.l2cCentralizerOddPart`, applied to `X = ⟨w⟩`, because the hypothesis `hQ0` on
`|Q₀|` gives exactly the two extra inputs that clause needs:

* `Q₀ = ⟨Inv H⟩` has order `2^{|P|} ≥ 4` and (by Ch. V §1 Prop. 1 (c), the involutions of `H`
  commute) is elementary abelian; since `w ∈ W = C_D(Inv H)` (Ch. II §4 Prop. 4) every element of
  `Q₀` centralises `w`, so `C_G(⟨w⟩)` contains a four-group (`HasFourGroup` is the 2-rank `≥ 2`
  hypothesis of the clause);
* `|K| = |Inv H| ≥ 2` (Ch. I §2 Prop. 2 (b) and `cardInvGeTwo`), and `w ∈ W` centralises
  `K = J(D,t)`, so `K#` supplies a non-trivial element normalising `⟨w⟩` (the `N_K(X) ≠ 1`
  hypothesis of the clause).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.Prove

theorem WfpfOddPart {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (hnil : Group.IsNilpotent ↥Q)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P) :
    ∀ w ∈ Work.ThmF.W H t, w ≠ 1 →
      Work.ThmF.oddPart Q ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ := by
  classical
  intro w hwW hw1
  -- ## 0. the standing context
  have hSit : Submission.Blueprint.Situation G := c.sit
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := c.split
  have hH : IsStronglyEmbedded H := hsplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  -- ## 1. `w` lies in `V = C_D(t)` and centralises `K = J(D,t)`
  have hwV : w ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t hwW
  have hwK : w ∈ Subgroup.centralizer (Work.ThmF.Kset H t : Set G) :=
    (Subgroup.mem_inf.mp hwW).2
  -- ## 2. Ch. II §4 Prop. 4: `W = D ⊓ C_G(Inv H)`, so `w` centralises `Inv H`
  have hWeq : Work.ThmF.W H t = Submission.Blueprint.twoPoint H t ⊓
      Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) := by
    have hP4 := (hC4 G hSit H hH t ht2 htH).2.2.2.2.1
    simpa only [Work.ThmF.W, Work.ThmF.Kset] using hP4
  have hwCinv : w ∈ Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) :=
    (Subgroup.mem_inf.mp (hWeq ▸ hwW)).2
  -- ## 3. the involutions of `H` commute pairwise (Ch. V §1 Prop. 1 (c))
  have hDtr := Work.ThmF.Bender.DTransitiveInv hH ht2 htH
  have hcentQ : ∀ u ∈ Submission.Blueprint.involutions (H : Set G), u ∈ Work.ThmF.centerOf Q :=
    Work.ThmF.ChV12.prop1c hSit H Q t hsplit hDtr hnil
  have hcommH : ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u := by
    intro u hu v hv
    have h1 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcentQ u hu)
    have h2 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcentQ v hv)
    exact h1.2 v h2.1
  -- ## 4. `C_G({w}) = C_G(⟨w⟩)`
  have hcent_eq : Subgroup.centralizer ({w} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure]
    exact (Subgroup.centralizer_closure ({w} : Set G)).symm
  -- ## 5. `Q₀sub H ≤ C_G(⟨w⟩)`
  have hQ0le_w : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Work.ThmF.Q0sub]
    refine (Subgroup.closure_le _).mpr ?_
    intro u hu
    rw [Work.ThmF.mem_Q0_iff] at hu
    rcases hu with ⟨huH, hu2⟩ | h1
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hwCinv) u ⟨huH, hu2⟩)
    · subst h1
      exact Subgroup.one_mem _
  have hQ0leX : Work.ThmF.Q0sub H ≤
      Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) :=
    hcent_eq ▸ hQ0le_w
  -- ## 6. `HasFourGroup (C_G(⟨w⟩))`, from the four-group of `Q₀sub H ≤ C_G(⟨w⟩)`
  have hQ0el := Work.ThmF.ChV12.Q0sub_elementary H hcommH
  have hcard4 : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hQ0]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Nat.card P := Nat.pow_le_pow_right (by norm_num) c.P_prime.two_le
  have hfour : Submission.Blueprint.HasFourGroup
      ↥(Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G)) := by
    have hexa : ∃ a ∈ Work.ThmF.Q0sub H, a ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hbot : Work.ThmF.Q0sub H = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      rw [hbot] at hcard4
      simp at hcard4
    obtain ⟨a, haQ0, ha1⟩ := hexa
    have haorder : orderOf a = 2 := (hQ0el.2.2.2 a haQ0 ha1).2
    have hexb : ∃ b ∈ Work.ThmF.Q0sub H, b ∉ Subgroup.zpowers a := by
      by_contra hcon
      push_neg at hcon
      have hdvd : Nat.card ↥(Work.ThmF.Q0sub H) ∣ Nat.card ↥(Subgroup.zpowers a) :=
        Subgroup.card_dvd_of_le hcon
      rw [Nat.card_zpowers, haorder] at hdvd
      have hle2 : Nat.card ↥(Work.ThmF.Q0sub H) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    obtain ⟨b, hbQ0, hbz⟩ := hexb
    have hb1 : b ≠ 1 := fun h => hbz (by rw [h]; exact Subgroup.one_mem _)
    have hborder : orderOf b = 2 := (hQ0el.2.2.2 b hbQ0 hb1).2
    have hba : b ≠ a := fun h => hbz (by rw [h]; exact Subgroup.mem_zpowers a)
    have hab : a * b = b * a := hQ0el.2.1 a haQ0 b hbQ0
    exact ⟨⟨a, hQ0leX haQ0⟩, ⟨b, hQ0leX hbQ0⟩,
      by rw [Subgroup.orderOf_mk]; exact haorder,
      by rw [Subgroup.orderOf_mk]; exact hborder,
      fun h => hba (Subtype.ext_iff.mp h).symm,
      by refine Subtype.ext ?_; push_cast; exact hab⟩
  -- ## 7. a non-trivial element `k ∈ K = J(D,t) = Kset H t` normalising `⟨w⟩`
  have hInv2 : 2 ≤ (Submission.Blueprint.involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardInvGeTwo hH hSit.1.1
  have hKcard : (Work.ThmF.Kset H t).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv (H := H) hH ht2 htH
  obtain ⟨k, hkK, hk1⟩ : ∃ k ∈ Work.ThmF.Kset H t, k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Work.ThmF.Kset H t ⊆ ({1} : Set G) := fun x hx => by
      rw [Set.mem_singleton_iff]; exact hcon x hx
    have hle : (Work.ThmF.Kset H t).ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard hsub
    rw [hKcard] at hle
    omega
  have hkN : k ∈ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
    have hkC_w : k ∈ Subgroup.centralizer ({w} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hwK) k hkK)
    have hkC : k ∈ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) :=
      hcent_eq ▸ hkC_w
    exact Subgroup.centralizer_le_normalizer _ hkC
  -- ## 8. Ch. V §2 Lemma 2 (c) at `X = ⟨w⟩`
  have hbot : Work.ThmF.oddPart Q ⊓
      Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) = ⊥ :=
    Work.ThmF.ChV3.l2cCentralizerOddPart hC4 hSit hsplit hnil
      (Subgroup.zpowers_le.mpr hwV) (fun h => hw1 (Subgroup.zpowers_eq_bot.mp h))
      ⟨k, hkK, hk1, hkN⟩ hfour
  rw [hcent_eq]
  exact hbot

end Work.ThmF.Prove
