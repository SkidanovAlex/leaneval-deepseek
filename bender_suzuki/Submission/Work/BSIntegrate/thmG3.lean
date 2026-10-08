import Mathlib
import Submission.Work.BSIntegrate.Defs
import Submission.Work.ThmG2.Assembly
import Submission.Work.ThmG2.Main
import Submission.Work.ThmG.Main
import Submission.Work.ThmF.ChV12.fpfOddPartProp
import Submission.Work.ThreePoints.BenderPrelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSIntegrate.thmG3` — Théorème G with the D1-repaired field 7

`Work.ThmG2.thmG2` needs the unconditional degree field `RankOneStructure2.degree`.  That field is
false when `Q` is a 2-group (then `oddPart Q = ⊥` and `excludingKernel H ⊥ = ∅`), so the honest
input is the corrected `Work.BSIntegrate.DegreeProp'`, which carries the extra hypothesis
`¬ IsPGroup 2 Q`.

This file assembles Théorème G from the *corrected* inputs: the rank-one structure of
`Work.ThmG2.RankOneStructure2` is built **after** the `by_contra hnotp : ¬ IsPGroup 2 Q`, so the
degree field may be fed by `DegreeProp' … hnotp`.  The remainder of the argument is
`Work.ThmG2.thmG2` verbatim.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open Classical
open Submission.Blueprint

namespace Work.BSIntegrate

open Work.ThmG

/-- **Théorème G** (Peterfalvi II, Ch. VI §1, p. 257): in a simple group in situation (B0)–(B2)
with a split rank-one datum `H = Q ⋊ D`, `t ∉ H`, which is not a Zassenhaus group and satisfies
`(B3)`, the normal complement `Q` is a 2-group.

Here the `FeitSibley` input (field 7) is the D1-corrected `DegreeProp'`, whose extra hypothesis
`¬ IsPGroup 2 Q` is available from the `by_contra`. -/
theorem thmG3 (hFT : Submission.Blueprint.FeitThompsonProp) (hFS : Submission.Blueprint.FeitSibleyProp) (hC4 : Submission.Blueprint.ChIIFourProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp) (h1 : Work.ThmG.KNeOneProp) (h3 : Work.ThmG.CoprimeDQProp) (h4 : Work.ThmG.FpfOddPartProp) (h5 : Work.ThmG2.ExistsLinearV2Prop) (h6 : Work.ThmG2.IndTwoV2Prop) (h7 : Work.BSIntegrate.DegreeProp') (h8 : Work.ThmG.VanishesOffProp) : Submission.Blueprint.ThmGProp := by
  intro G _ _ hSit hsimple H Q t hsplit hnotZ hB3
  letI : Fintype G := Fintype.ofFinite G
  by_contra hnotp
  have hh : RankOneHyp G H Q t := ⟨hSit, hsimple, hsplit, hnotZ, hB3⟩
  have hstr : Work.ThmG2.RankOneStructure2 G H Q t :=
    ⟨h1 G H Q t hh, dNeBotProp G H Q t hh, h3 G H Q t hh, h4 G H Q t hh, h5 G H Q t hh,
      h6 G H Q t hh, h7 G H Q t hh hnotp, h8 G H Q t hh⟩
  -- the rest is `Work.ThmG2.thmG2` verbatim
  have hQnil : Group.IsNilpotent Q :=
    nilpotent_of_K_ne_one hSit hC4 hTh hsplit hstr.K_ne_one
  obtain ⟨hsupQ, hinfQ, hcommQ, hcopS, hoddQ₁, hnilS, hcardQ, hQ₁ne⟩ :=
    nilpotent_two_odd_split Q hQnil
  have hQ₁Q : oddPart Q ≤ Q := oddPart_le Q
  have hQ₁H : oddPart Q ≤ H := le_trans hQ₁Q hsplit.le
  have hQ₁ne' : oddPart Q ≠ ⊥ := hQ₁ne hnotp
  have hDnorm : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans inf_le_left hsplit.normal
  have hcardHD : Nat.card ↥H = Nat.card ↥Q * Nat.card ↥(twoPoint H t) := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := Q)
      (K := twoPoint H t) hDnorm
    rw [hsplit.sup_eq, hsplit.inf_eq] at h
    simpa using h
  have hEvenH : Even (Nat.card ↥H) := hsplit.stronglyEmbedded.2.1
  have hOddD : Odd (Nat.card ↥(twoPoint H t)) := hsplit.stronglyEmbedded.2.2 t hsplit.not_mem
  have hEvenQ : Even (Nat.card ↥Q) := even_of_eq_mul hcardHD hEvenH hOddD
  have hS2 : 2 ≤ Nat.card ↥(twoPart Q) :=
    two_le_of_eq_mul hcardQ.symm hEvenQ hoddQ₁ Nat.card_pos.ne'
  have hQ₁3 : 3 ≤ Nat.card ↥(oddPart Q) :=
    three_le_of_odd_ne_one hoddQ₁ (fun h1 => hQ₁ne' (Subgroup.card_eq_one.mp h1))
  have hD3 : 3 ≤ Nat.card ↥(twoPoint H t) :=
    three_le_of_odd_ne_one hOddD (fun h1 => hstr.D_ne_bot (Subgroup.card_eq_one.mp h1))
  have hQ₁N : ((oddPart Q).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQ₁H]
    exact oddPart_le_normalizer hsplit.normal
  have hQ₁card : Nat.card ↥((oddPart Q).subgroupOf H) = Nat.card ↥(oddPart Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₁H).toEquiv
  have hQ₁pos : Nat.card ↥(oddPart Q) ≠ 0 := Nat.card_pos.ne'
  have hindex : ((oddPart Q).subgroupOf H).index
      = Nat.card ↥(twoPart Q) * Nat.card ↥(twoPoint H t) := by
    have h1 : Nat.card ↥((oddPart Q).subgroupOf H) * ((oddPart Q).subgroupOf H).index
        = Nat.card ↥H := Subgroup.card_mul_index _
    rw [hQ₁card] at h1
    exact index_eq_of_mul_eq h1 hcardHD hcardQ.symm hQ₁pos
  have hindexQ : H.index = Nat.card ↥Q + 1 := rankOne_index hsplit
  have hHindexOdd : Odd H.index := by
    rw [hindexQ]
    exact hEvenQ.add_one
  have hnot2Q₁ : ¬ IsPGroup 2 (oddPart Q) := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    have hn0 : n = 0 := by
      by_contra hn0
      have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      rw [← hn] at hdvd
      have hmod : Nat.card ↥(oddPart Q) % 2 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp (hn ▸ hdvd)
      have hodd : Nat.card ↥(oddPart Q) % 2 = 1 := Nat.odd_iff.mp hoddQ₁
      omega
    rw [hn0, pow_zero] at hn
    exact hQ₁ne' (Subgroup.card_eq_one.mp hn)
  have hFSdata : 2 ≤ (excludingKernel H (oddPart Q)).card ∧
      Work.Coherence.Coherent (excludingKernel H (oddPart Q)) (indLinear H) :=
    hFS G H Q (twoPoint H t) (twoPart Q) (oddPart Q)
      hsplit.stronglyEmbedded.1 hsplit.le hsplit.normal inf_le_left
      hsplit.inf_eq hsplit.sup_eq hstr.coprime (rankOne_isTI hsplit)
      hsupQ hinfQ hcommQ hcopS hnilS hstr.fpf_oddPart hnot2Q₁ hOddD
  obtain ⟨hcard2, hcoh⟩ := hFSdata
  obtain ⟨lam, hlam, hlam1, hlamne, hlamQ, hlamK⟩ := hstr.exists_linear
  obtain ⟨f₁, hf1, f₂, hf2, hfne, hind⟩ := hstr.ind_two lam hlam hlam1 hlamne hlamQ hlamK
  -- the degree count
  obtain ⟨f, hf, hfne1, hker⟩ :=
    degree_count_engine hQ₁H hQ₁N hsplit.normal (rankOne_isTI hsplit)
      hsplit.sup_eq hsplit.inf_eq hstr.coprime hD3 hS2 hQ₁3 hcardHD hcardQ.symm hindex
      hcoh hcard2 hstr.vanishes_off hstr.degree hlam hlam1 hlamQ hlamne hf1 hf2 hfne hind
      hindexQ hHindexOdd
  -- `ker f` is a non-trivial proper normal subgroup
  obtain ⟨N, hNnorm, hNset⟩ := Work.CharCore.charKernel_subgroup hf
  have hQ₁Nle : oddPart Q ≤ N := by
    intro x hx
    show x ∈ (N : Set G)
    rw [hNset]
    exact hker ⟨x, hQ₁H hx⟩ hx
  have hNbot : N ≠ ⊥ := by
    rintro rfl
    exact hQ₁ne' (le_bot_iff.mp hQ₁Nle)
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hconst : ∀ x : G, f x = f 1 := by
      intro x
      have hxN : x ∈ (N : Set G) := by
        rw [htop]
        exact Subgroup.mem_top x
      rw [hNset] at hxN
      exact hxN
    exact hfne1 (irr_eq_one_of_forall_eq_one hf hconst)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple N hNnorm with h | h
  · exact hNbot h
  · exact hNtop h

end Work.BSIntegrate
