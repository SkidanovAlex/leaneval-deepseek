import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.L5Aux
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.ThmF.Bender.cardInvertedMulCardCentralizer
import Submission.Work.ThmF.ChV12.L5route

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5cruxAux` — the shape of the remaining case of Ch. V §2 Lemma 5

The remaining gap of `Work.ThmF.ChV12.lemma5` is the case

  `Q = Q0sub H`, `X5 H t = ⊤`, `V = centD H t ≠ ⊥`  (all other cases are proved in `L5route.lean`).

This file collects, with proofs, the structural consequences of `X5 H t = ⊤` that any proof of
that case must use (and that make the case very rigid):

* `X5_eq_top_imp_twoPoint_eq_Ksub`: `X5 H t = ⊤` forces `D = twoPoint H t = Ksub H t = ⟨Kset H t⟩`
  (because `D ≤ X5 ⊓ H = bor H t = Q0sub H · Ksub H t` and `Q0sub H ⊓ D = ⊥`).
* `X5_eq_top_imp_centD_le_Ksub`: hence `V ⊆ Ksub H t` — the "bad case" of the wall.
* `X5_eq_top_imp_centD_ne_bot_imp_W_eq_bot`: with `V ≠ ⊥`, the branch `W ≠ ⊥` of Prop. 2
  (`Ksub_eq_Kset_of_W_ne_bot`) would give `|Ksub| = |Kset| = |Q0sub H| - 1`, contradicting
  `|Ksub| = |D| = |V|·|Q0sub H| - |V|`; hence `W = ⊥`.
* `X5_eq_top_imp_centD_ne_bot_imp_centralizer_eq_bot`: with `V ≠ ⊥` also
  `D ⊓ C_G(Q0sub H) = ⊥`, so `D` acts faithfully on the elementary abelian group
  `Q0sub H` and (via `Kset_regular`) is a subgroup of `GL(n,2)`, `2ⁿ = |Q0sub H|`, containing
  the sharply transitive subset `Kset H t` of size `2ⁿ - 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- If `X5 H t = ⊤` then `Q = Q0sub H` (because `X5 ⊓ Q = Q0sub H`). -/
theorem X5_eq_top_imp_Q_eq_Q0sub (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hX : Work.ThmF.Lemma5.X5 H t = ⊤) : Q = Work.ThmF.Q0sub H := by
  have h1 := Work.ThmF.L5.X5_inf_Q hC4 h
  rw [hX, top_inf_eq] at h1
  exact h1

/-- **In the case `X5 H t = ⊤`, `D = twoPoint H t` is `Ksub H t`.**  Indeed `D ≤ X5 ⊓ H = bor`,
`bor = Q0sub H · Ksub H t`, and `Q0sub H ⊓ D = ⊥`. -/
theorem X5_eq_top_imp_twoPoint_eq_Ksub (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hX : Work.ThmF.Lemma5.X5 H t = ⊤) : Submission.Blueprint.twoPoint H t = Work.ThmF.Ksub H t := by
  have hle : Submission.Blueprint.twoPoint H t ≤ Work.ThmF.Ksub H t := by
    intro d hd
    have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).1
    have hdX : d ∈ Work.ThmF.Lemma5.X5 H t := by rw [hX]; exact Subgroup.mem_top d
    have hdB : d ∈ Work.ThmF.L5.bor H t := by
      have h1 := Work.ThmF.L5.X5_inf_H hC4 h
      rw [← h1]
      exact Subgroup.mem_inf.mpr ⟨hdX, hdH⟩
    obtain ⟨q, hq, k, hk, hkq⟩ := Work.ThmF.L5.bor_factor hC4 h hdB
    have hqD : q ∈ Submission.Blueprint.twoPoint H t := by
      have h1 : q = k⁻¹ * d := by rw [← hkq]; group
      rw [h1]
      exact (Submission.Blueprint.twoPoint H t).mul_mem
        ((Submission.Blueprint.twoPoint H t).inv_mem (Work.ThmF.Ksub_le_twoPoint (H := H) t hk)) hd
    have hq1 : q = 1 := by
      have h2 : q ∈ Q ⊓ Submission.Blueprint.twoPoint H t :=
        Subgroup.mem_inf.mpr ⟨Work.ThmF.L5.Q0sub_le_Q h hq, hqD⟩
      rw [h.split.inf_eq] at h2
      exact Subgroup.mem_bot.mp h2
    rw [← hkq, hq1, mul_one]
    exact hk
  exact le_antisymm hle (Work.ThmF.Ksub_le_twoPoint (H := H) t)

/-- **In the case `X5 H t = ⊤` one has `V ⊆ Ksub H t`** (the "bad case" of Prop. 2). -/
theorem X5_eq_top_imp_centD_le_Ksub (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hX : Work.ThmF.Lemma5.X5 H t = ⊤) :
    Submission.Blueprint.centD H t ≤ Work.ThmF.Ksub H t := by
  rw [← X5_eq_top_imp_twoPoint_eq_Ksub hC4 h hX]
  exact inf_le_left

/-- **In the case `X5 H t = ⊤` with `V ≠ ⊥`, one has `W = C_V(Kset H t) = ⊥`.**  Otherwise the
branch `W ≠ ⊥` of Prop. 2 gives `Ksub = Kset`, i.e. `|Ksub| = |Q0sub H| - 1`, while
`X5 = ⊤` gives `|Ksub| = |D| = |V| · |Kset|` with `|V| > 1` and `|Kset| = |Q0sub H| - 1`. -/
theorem X5_eq_top_imp_centD_ne_bot_imp_W_eq_bot (hC4 : ChIIFourProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hX : Work.ThmF.Lemma5.X5 H t = ⊤)
    (hV : Submission.Blueprint.centD H t ≠ ⊥) : Work.ThmF.W H t = ⊥ := by
  by_contra hW
  have hKeq : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    Ksub_eq_Kset_of_W_ne_bot hC4 h hW
  have hDK : Submission.Blueprint.twoPoint H t = Work.ThmF.Ksub H t :=
    X5_eq_top_imp_twoPoint_eq_Ksub hC4 h hX
  have hcard1 : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Kset H t).ncard := by
    rw [← hKeq]
    exact (Nat.card_coe_set_eq _).symm
  have hcard2 : Nat.card ↥(Work.ThmF.Kset H t) = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv h.split.stronglyEmbedded h.split.invol h.split.not_mem
  -- `|D| = |Ksub| = |Kset|`
  have hDV : Nat.card ↥(Submission.Blueprint.twoPoint H t) = (Work.ThmF.Kset H t).ncard := by
    rw [hDK]; exact hcard1
  have hsplitcard : Nat.card ↥(Submission.Blueprint.centD H t) * (Work.ThmF.Kset H t).ncard
      = Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
    Work.ThmF.card_centD_mul_card_Kset (H := H) (t := t)
      (Work.ThmF.IsSplitRankOne.toData h.split)
  have hchain : Nat.card ↥(Submission.Blueprint.centD H t) * (Work.ThmF.Kset H t).ncard
      = (Work.ThmF.Kset H t).ncard := by
    rw [hsplitcard, hDV]
  have hk1 : 1 ≤ (Work.ThmF.Kset H t).ncard := by
    obtain ⟨x, hx, -⟩ := Work.ThmF.L5.exists_mem_Kset_ne_one h.sit h.split
    exact Nat.one_le_iff_ne_zero.mpr (Set.ncard_ne_zero_of_mem hx (Set.toFinite _))
  have hV1 : Nat.card ↥(Submission.Blueprint.centD H t) = 1 := by
    by_contra hne
    have hV2 : 2 ≤ Nat.card ↥(Submission.Blueprint.centD H t) := by
      have hpos := Nat.card_pos (α := ↥(Submission.Blueprint.centD H t))
      omega
    have h2k : 2 * (Work.ThmF.Kset H t).ncard ≤ (Work.ThmF.Kset H t).ncard := by
      calc 2 * (Work.ThmF.Kset H t).ncard
          ≤ Nat.card ↥(Submission.Blueprint.centD H t) * (Work.ThmF.Kset H t).ncard :=
            Nat.mul_le_mul_right _ hV2
        _ = (Work.ThmF.Kset H t).ncard := hchain
    omega
  exact hV (Subgroup.card_eq_one.mp hV1)

/-- **In the case `X5 H t = ⊤` with `V ≠ ⊥`, `D` acts faithfully on `Q0sub H`:** from the P4
clause of `ChIIFourProp` (`W = D ⊓ C_G(Inv H)`) and `W = ⊥` (`X5_eq_top_imp_centD_ne_bot_imp_W_eq_bot`). -/
theorem X5_eq_top_imp_centD_ne_bot_imp_centralizer_eq_bot (hC4 : ChIIFourProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hX : Work.ThmF.Lemma5.X5 H t = ⊤)
    (hV : Submission.Blueprint.centD H t ≠ ⊥) :
    Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) = ⊥ := by
  have hW : Work.ThmF.W H t = ⊥ := X5_eq_top_imp_centD_ne_bot_imp_W_eq_bot hC4 h hX hV
  have hP4 := (hC4 G h.sit H h.split.stronglyEmbedded t h.split.invol h.split.not_mem).2.2.2.2.1
  have hle : Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (Work.ThmF.Q0sub H : Set G)
      ≤ Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (fun x hx =>
      Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hx)))
  have hle2 : Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (Work.ThmF.Q0sub H : Set G)
      ≤ Submission.Blueprint.centD H t ⊓
        Subgroup.centralizer
          (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t : Set G) := by
    rw [hP4]; exact hle
  have hbot : Submission.Blueprint.centD H t ⊓
      Subgroup.centralizer
        (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t : Set G) = ⊥ := hW
  rw [hbot] at hle2
  exact le_bot_iff.mp hle2

end Work.ThmF.ChV12
