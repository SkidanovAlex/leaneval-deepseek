import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.L5Aux
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.ThmF.ChV12.X5_rankOne_of
import Submission.Work.ThmF.ChV12.L5simpleX5
import Submission.Work.ThmF.ChV12.L5twoTransitive
import Submission.Work.ThmF.ChV12.L5splitRankOne
import Submission.Work.ThmF.ChV12.L5zassenhaus
import Submission.Work.ThmF.ChV12.L5crux
import Submission.Work.ThmF.ChV12.lemma2a_card_omega
import Submission.Work.ThmF.ChV12.prop2v2
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmF.Bender.cardInvertedMulCardCentralizer
import Submission.Work.Models.models
import Submission.Work.Endgame.isSimpleBenderGroup_of_benderConclusion
import Submission.Work.RankOneUniqueness.recognize
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.ZassenhausPSL2.Model.psl2_datum
import Submission.Work.ZassenhausPSL2.ZassenhausPSL2OfQCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5route` — the proof chain of Ch. V §2 Lemma 5, modulo `L5crux`

This file assembles, with everything *else* proved, the reduction of the target

  `∃ n ≥ 2, |Q0sub H| = 2ⁿ ∧ X5 H t ≃* PSL2Model n`   (`Hyp5` + `ChIIFourProp`)

to the single remaining statement `Work.ThmF.ChV12.L5crux` (Ch. V §1 Prop. 2 in the branch
`V ≠ 1`, `W = 1`, i.e. `Ksub H t = Kset H t` there).

Contents.

* `card_G_eq`: `|G| = |Q| · |D| · (1 + |Q|)` (from `lemma2a_card_omega` and `split_card_H`).
* `X5_ne_top_of_Q_ne_Q0sub`: if `Q ≠ Q0sub H` then `X5 H t ≠ ⊤` (because `X5 ⊓ Q = Q0sub H`);
  in particular `|X5| < |G|` there, so `(B1)` from `Hyp5.sit` applies to `↥(X5 H t)`.
* `hasFourGroup_X5` / `benderHyp_X5`: `↥(X5 H t)` satisfies `(B0)`.
* `isSimpleBenderGroup_X5_of`: `(B1)` + `Endgame` give `IsSimpleBenderGroup ↥(X5 H t)`.
* `Ksub_eq_Kset_of_isSimpleBenderGroup`: the model facts (`Work.Models.models_prop`) give
  `Ksub H t = Kset H t` from `IsSimpleBenderGroup ↥(X5 H t)`.
* `Ksub_eq_Kset_of_X5_ne_top`: hence `Ksub = Kset` whenever `X5 H t ≠ ⊤`.  **The crux is needed
  exactly in the remaining case `Q = Q0sub H` and `X5 = ⊤`.**
* the two easy branches of Prop. 2 (`centD H t = ⊥`, `W H t ≠ ⊥`) are re-proved here (they are
  `private` in `L5prop2.lean`), and `Ksub_eq_Kset_full` combines them with `L5crux`.
* `lemma5_of_Ksub_eq_Kset`: the target, given `Ksub = Kset`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-! ## Cardinalities -/

/-- `|G| = |Q| · |D| · (1 + |Q|)`, where `D = H ⊓ Hᵗ`: `|G| = |H| · |G : H|` with
`|H| = |Q| · |D|` and `|G : H| = 1 + |Q|` (`lemma2a_card_omega`). -/
theorem card_G_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) :
    Nat.card G = Nat.card ↥Q * Nat.card ↥(twoPoint H t) * (1 + Nat.card ↥Q) := by
  have hΩ : Nat.card (Work.DoubleTransitivity.Omega H) = Nat.card ↥Q + 1 :=
    Work.ThmF.ChV12.lemma2a_card_omega h
  have hidx : Nat.card ↥H * Nat.card (Work.DoubleTransitivity.Omega H) = Nat.card G := by
    have h1 := Subgroup.card_mul_index H
    rwa [Subgroup.index_eq_card] at h1
  rw [← hidx, hΩ, Work.ThmF.split_card_H h]
  ring

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem natCard_lt_of_ne_top {M : Subgroup G} (h : M ≠ ⊤) : Nat.card ↥M < Nat.card G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hdvd : Nat.card ↥M ∣ Nat.card G := Subgroup.card_subgroup_dvd_card M
  have hne : Nat.card ↥M ≠ Nat.card G := by
    intro heq
    exact h (Subgroup.eq_top_of_card_eq M heq)
  exact lt_of_le_of_ne (Nat.le_of_dvd hpos hdvd) hne

/-! ## `(B0)` and `(B1)` for `↥(X5 H t)` -/

/-- `X5 H t ≠ ⊤` as soon as `Q ≠ Q0sub H`, because `X5 ⊓ Q = Q0sub H`. -/
theorem X5_ne_top_of_Q_ne_Q0sub (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hne : Q ≠ Work.ThmF.Q0sub H) : Work.ThmF.Lemma5.X5 H t ≠ ⊤ := by
  intro htop
  apply hne
  have h1 := Work.ThmF.L5.X5_inf_Q hC4 h
  rw [htop, top_inf_eq] at h1
  exact h1

/-- `↥(X5 H t)` has a four-group: the involutions of `H` lie in `X5`, commute pairwise
(`L5.involutions_commute`), and there are at least two of them (`Bender.cardInvGeTwo`). -/
theorem hasFourGroup_X5 (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    HasFourGroup ↥(Work.ThmF.Lemma5.X5 H t) := by
  have hcomm := Work.ThmF.L5.involutions_commute h.sit hC4 h.split
  have h2 : 2 ≤ (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardInvGeTwo h.split.stronglyEmbedded h.sit.1.1
  have h1 : 1 < (involutions (H : Set G)).ncard := by omega
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (Set.one_lt_ncard (s := involutions (H : Set G)) (Set.toFinite _)).mp h1
  have huX : u ∈ Work.ThmF.Lemma5.X5 H t :=
    Work.ThmF.L5.Q0sub_le_X5 (H := H) (t := t)
      (Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hu))
  have hvX : v ∈ Work.ThmF.Lemma5.X5 H t :=
    Work.ThmF.L5.Q0sub_le_X5 (H := H) (t := t)
      (Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hv))
  refine ⟨⟨u, huX⟩, ⟨v, hvX⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact hu.2
  · rw [Subgroup.orderOf_mk]; exact hv.2
  · intro hcon
    exact huv (congrArg Subtype.val hcon)
  · apply Subtype.ext
    exact hcomm u hu v hv

/-- `(B0)` for `↥(X5 H t)`: a four-group (`hasFourGroup_X5`) and the strongly embedded
subgroup `bor H t = Q0sub H ⊔ Ksub H t`. -/
theorem benderHyp_X5 (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    BenderHyp ↥(Work.ThmF.Lemma5.X5 H t) :=
  ⟨hasFourGroup_X5 hC4 h, ⟨_, bor_stronglyEmbedded hC4 h⟩⟩

/-- The induction hypothesis `(B1)` of `Hyp5` applies to `↥(X5 H t)`, and `Endgame` turns its
conclusion into `IsSimpleBenderGroup`. -/
theorem isSimpleBenderGroup_X5_of (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hB : BenderHyp ↥(Work.ThmF.Lemma5.X5 H t))
    (hlt : Nat.card ↥(Work.ThmF.Lemma5.X5 H t) < Nat.card G)
    (hsimple : IsSimpleGroup ↥(Work.ThmF.Lemma5.X5 H t)) :
    LeanEval.GroupTheory.Defs.IsSimpleBenderGroup ↥(Work.ThmF.Lemma5.X5 H t) := by
  haveI := hsimple
  exact Work.Endgame.isSimpleBenderGroup_of_benderConclusion Work.Models.models_prop
    (h.sit.2.1 _ hlt hB) (Work.Endgame.HasFourGroup.even_natCard hB.1)

/-- **The model facts give `Ksub = Kset`**, once `↥(X5 H t)` is a simple Bender group: for the
strongly embedded `B = bor H t` and the involution `tX ∉ B`, `ModelFactsProp` produces a cyclic
subgroup whose carrier is `invertedBy (twoPoint B tX) tX`; pulling back along
`twoPoint_bor_subgroupOf` that carrier is exactly `Kset H t`. -/
theorem Ksub_eq_Kset_of_isSimpleBenderGroup (hC4 : ChIIFourProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup ↥(Work.ThmF.Lemma5.X5 H t)) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  classical
  have hBse : IsStronglyEmbedded ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    bor_stronglyEmbedded hC4 h
  obtain ⟨-, hmain⟩ := (Work.Models.models_prop ↥(Work.ThmF.Lemma5.X5 H t) hY).2.2.2
    ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) hBse
  obtain ⟨S, K, -, -, -, -, -, hKset, -, -⟩ :=
    hmain (Work.ThmF.Lemma5.tX H t) (Work.ThmF.L5.orderOf_tX h) (Work.ThmF.L5.tX_notMem_bor h)
  have htw : twoPoint ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
      (Work.ThmF.Lemma5.tX H t) = ((Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    Work.ThmF.L5.twoPoint_bor_subgroupOf hC4 h
  -- membership characterisation of the model subgroup `K`
  have hKmem : ∀ y : ↥(Work.ThmF.Lemma5.X5 H t),
      y ∈ (K : Set ↥(Work.ThmF.Lemma5.X5 H t)) ↔
        ((y : G) ∈ Work.ThmF.Ksub H t ∧ t * (y : G) * t⁻¹ = (y : G)⁻¹) := by
    intro y
    have hy : y ∈ (K : Set ↥(Work.ThmF.Lemma5.X5 H t)) ↔
        y ∈ invertedBy ((Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
          (Work.ThmF.Lemma5.tX H t) := by
      rw [hKset, htw]
    rw [hy]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Subgroup.mem_subgroupOf.mp h1, ?_⟩
      have hmap := congrArg (fun z : ↥(Work.ThmF.Lemma5.X5 H t) => (z : G)) h2
      simpa using hmap
    · rintro ⟨h1, h2⟩
      refine ⟨Subgroup.mem_subgroupOf.mpr h1, ?_⟩
      apply Subtype.ext
      show t * (y : G) * t⁻¹ = (y : G)⁻¹
      exact h2
  -- the carrier of `K` in `G` is exactly `Kset H t`
  have hcarrier : ∀ x : G,
      x ∈ K.map (Work.ThmF.Lemma5.X5 H t).subtype ↔ x ∈ Work.ThmF.Kset H t := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rw [← hyx]
      obtain ⟨h1, h2⟩ := (hKmem y).mp hy
      exact ⟨Work.ThmF.Ksub_le_twoPoint (H := H) t h1, h2⟩
    · intro hx
      have hxK : x ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hx
      have hxX : x ∈ Work.ThmF.Lemma5.X5 H t := Work.ThmF.L5.Ksub_le_X5 hxK
      refine Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, ?_, rfl⟩
      exact (hKmem ⟨x, hxX⟩).mpr ⟨hxK, (Work.ThmF.mem_Kset_iff.mp hx).2⟩
  have hle : Work.ThmF.Ksub H t ≤ K.map (Work.ThmF.Lemma5.X5 H t).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    exact (hcarrier x).mpr hx
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    exact (hcarrier x).mp (hle hx)
  · intro x hx
    exact Work.ThmF.Kset_le_Ksub H t hx

/-- **`Ksub = Kset` whenever `X5 H t ≠ ⊤`** (i.e. outside the crux case): `(B1)` gives that
`↥(X5 H t)` is a simple Bender group, and the model facts then give the statement. -/
theorem Ksub_eq_Kset_of_X5_ne_top (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hnt : Work.ThmF.Lemma5.X5 H t ≠ ⊤) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
  Ksub_eq_Kset_of_isSimpleBenderGroup hC4 h
    (isSimpleBenderGroup_X5_of h (benderHyp_X5 hC4 h) (natCard_lt_of_ne_top hnt)
      (Work.ThmF.ChV12.L5simpleX5 hC4 h))

/-- **`Ksub = Kset` when `Q ≠ Q0sub H`** (a special case of `Ksub_eq_Kset_of_X5_ne_top`). -/
theorem Ksub_eq_Kset_of_Q_ne_Q0sub (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hne : Q ≠ Work.ThmF.Q0sub H) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
  Ksub_eq_Kset_of_X5_ne_top hC4 h (X5_ne_top_of_Q_ne_Q0sub hC4 h hne)

/-! ## The two easy branches of Prop. 2 (private in `L5prop2.lean`) -/

/-- Case `V = C_D(t) = 1`: then `|K| = |D|` by App. I (1)(b), and `K ⊆ D`, so `K = D`
is a subgroup. -/
theorem Ksub_eq_Kset_of_centD_bot (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hV : centD H t = ⊥) : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  have hsplit : IsSplitRankOne H Q t := h.split
  have hcard := Work.ThmF.card_centD_mul_card_Kset (H := H) (t := t)
    (Work.ThmF.IsSplitRankOne.toData hsplit)
  rw [hV, Subgroup.card_bot, one_mul] at hcard
  have hKD : Work.ThmF.Kset H t ⊆ (twoPoint H t : Set G) := Work.ThmF.Kset_subset H t
  have hDcard : (twoPoint H t : Set G).ncard = (Work.ThmF.Kset H t).ncard := by
    rw [← Nat.card_coe_set_eq]; exact hcard.symm
  have hKeq : Work.ThmF.Kset H t = (twoPoint H t : Set G) :=
    Set.eq_of_subset_of_ncard_le hKD (le_of_eq hDcard)
  rw [Work.ThmF.Ksub, hKeq, Subgroup.closure_eq]

/-- Case `W = C_V(K) ≠ 1`: take `X = W`; all of `K` centralises `X`, so clause P3 of
`ChIIFourProp` returns a cyclic `N = K ∩ N_G(X) = K`, whence `K` is a subgroup. -/
theorem Ksub_eq_Kset_of_W_ne_bot (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hW : Work.ThmF.W H t ≠ ⊥) : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  have hsplit : IsSplitRankOne H Q t := h.split
  have hP3 := (hC4 G h.sit H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.2.2.1
  obtain ⟨k0, hk0, hk01⟩ := Work.ThmF.L5.exists_mem_Kset_ne_one h.sit hsplit
  have hKN : Work.ThmF.Kset H t ⊆ (Subgroup.normalizer (Work.ThmF.W H t : Set G) : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro x
    constructor
    · intro hx
      have hxcent : x ∈ Subgroup.centralizer (Work.ThmF.Kset H t : Set G) :=
        (Subgroup.mem_inf.mp hx).2
      have hcx : k * x = x * k := Subgroup.mem_centralizer_iff.mp hxcent k hk
      have : k * x * k⁻¹ = x := by rw [hcx]; group
      rw [this]; exact hx
    · intro hx
      have hxcent : k * x * k⁻¹ ∈ Subgroup.centralizer (Work.ThmF.Kset H t : Set G) :=
        (Subgroup.mem_inf.mp hx).2
      have hki : k⁻¹ ∈ Work.ThmF.Kset H t := Work.ThmF.L5.Kset_inv_mem h hk
      have hcomm : (k * x * k⁻¹) * k⁻¹ = k⁻¹ * (k * x * k⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hxcent k⁻¹ hki).symm
      have hxe : x = k * x * k⁻¹ := by
        calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
          _ = ((k * x * k⁻¹) * k⁻¹) * k := by rw [hcomm]
          _ = k * x * k⁻¹ := by group
      rw [hxe]; exact hx
  obtain ⟨-, -, -, hN⟩ := hP3 (Work.ThmF.W H t) hW (Work.ThmF.W_le_centD H t)
    ⟨k0, hk0, hk01, hKN hk0⟩
  obtain ⟨N, hNset, -, hNcyc⟩ := hN
  have hNset' : (N : Set G) = Work.ThmF.Kset H t := by
    rw [hNset]
    exact Set.Subset.antisymm Set.inter_subset_left (fun x hx => ⟨hx, hKN hx⟩)
  have hKsub_eq : Work.ThmF.Ksub H t = N := by
    refine le_antisymm ?_ ?_
    · show Subgroup.closure (Work.ThmF.Kset H t) ≤ N
      refine (Subgroup.closure_le N).mpr ?_
      intro x hx
      rw [hNset']; exact hx
    · intro x hx
      exact Work.ThmF.Kset_le_Ksub H t (by rw [← hNset']; exact hx)
  rw [hKsub_eq, hNset']

/-! ## The full statement of Prop. 2 -/

/-- **`K = J(D,t)` is a subgroup in the branch `V ≠ 1`, `W = 1`**, from the refined crux. -/
theorem Ksub_eq_Kset_of_V_ne_bot_W_bot (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hV : centD H t ≠ ⊥) (hW : Work.ThmF.W H t = ⊥) (hcrux : Work.ThmF.ChV12.L5cruxProp) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  by_cases hQ : Q = Work.ThmF.Q0sub H
  · rcases hcrux hC4 h hQ with hnt | hbot
    · exact Ksub_eq_Kset_of_X5_ne_top hC4 h hnt
    · exact absurd hbot hV
  · exact Ksub_eq_Kset_of_Q_ne_Q0sub hC4 h hQ

/-- **`K = J(D,t)` is a subgroup** (Peterfalvi II Ch. V §1 Prop. 2), for `Hyp5` data. -/
theorem Ksub_eq_Kset_full (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hcrux : Work.ThmF.ChV12.L5cruxProp) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  by_cases hV : centD H t = ⊥
  · exact Ksub_eq_Kset_of_centD_bot hC4 h hV
  · by_cases hW : Work.ThmF.W H t = ⊥
    · exact Ksub_eq_Kset_of_V_ne_bot_W_bot hC4 h hV hW hcrux
    · exact Ksub_eq_Kset_of_W_ne_bot hC4 h hW

/-- **Peterfalvi II, Ch. V §2 Lemma 5**: `X = ⟨Q₀, K, t⟩ ≃ PSL(2, 2ⁿ)`, `|Q₀| = 2ⁿ`, from
`Hyp5` and `ChIIFourProp`, *given* that `K = J(D,t)` is the subgroup `Ksub H t` (Prop. 2).
This is `X5isoPSL2_of` with its unused `FeitThompsonProp` hypothesis and its appeal to the
still-open `L5prop2` replaced by the explicit `hKsub`. -/
theorem lemma5_of_Ksub_eq_Kset (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n ∧
      Nonempty (↥(Work.ThmF.Lemma5.X5 H t) ≃* LeanEval.GroupTheory.Defs.PSL2Model n) := by
  classical
  have hcomm := Work.ThmF.L5.involutions_commute h.sit hC4 h.split
  haveI : IsSimpleGroup ↥(Work.ThmF.Lemma5.X5 H t) := L5simpleX5 hC4 h
  haveI : Fintype ↥(Work.ThmF.Lemma5.X5 H t) := Fintype.ofFinite _
  have hsplit : IsSplitRankOne ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
      ((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t))
      (Work.ThmF.Lemma5.tX H t) := L5splitRankOne hC4 h
  have hz : IsZassenhaus ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    L5zassenhaus_of_Ksub_eq_Kset hC4 h hKsub
  have h2 : IsPGroup 2 ↥((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    Work.ThmF.L5.isPGroup_two_Q0sub_sub (H := H) hcomm
  have hab : IsAbelianSubgroup
      ((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    Work.ThmF.L5.isAbelianSubgroup_Q0sub_sub (H := H) hcomm
  have hcz := Work.ZassenhausPSL2.FeitCln.card_excl_eq_one hsplit hz h2 hab
  have hmul := Work.ZassenhausPSL2.Feit.card_excl hsplit hz h2 hab
  have hcard := Work.ZassenhausPSL2.ZData.card_Q_eq hcz hmul
  obtain ⟨n, hn, e, hf⟩ := Work.ZassenhausPSL2.ZData.psl2_coords hsplit hz h2 hab hcard
  refine ⟨n, hn, ?_, ?_⟩
  · rw [← Work.ThmF.L5.card_subgroupOf_Q0sub (H := H)]
    exact (Nat.card_congr e.toEquiv).trans
      (Work.ThmF.L5.card_multiplicative_galoisField n (by omega))
  · obtain ⟨M⟩ := Work.ZassenhausPSL2.Model.psl2_datum n hn
    exact Work.RankOneUniqueness.recognize Work.RankOneUniqueness.rankOneQUniqueness
      hsplit M e hf

/-- **The target of `Work.ThmF.ChV12.lemma5`.** -/
theorem lemma5_of_route (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hcrux : Work.ThmF.ChV12.L5cruxProp) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n ∧
      Nonempty (↥(Work.ThmF.Lemma5.X5 H t) ≃* LeanEval.GroupTheory.Defs.PSL2Model n) :=
  lemma5_of_Ksub_eq_Kset hC4 h (Ksub_eq_Kset_full hC4 h hcrux)

end Work.ThmF.ChV12
