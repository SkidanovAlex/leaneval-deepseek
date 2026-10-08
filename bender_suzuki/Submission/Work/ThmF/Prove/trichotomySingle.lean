
import Mathlib
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.DoubleTransitivity.Sec5.inductionStep
import Submission.Work.Models.Port.BenderBasic
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.benderSTProp
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.PSU3.StageA.isSplitRankOneTransfer
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.PSU3.StageA.modelDataBorel
import Submission.Work.PSU3.StageA.orderOfMapEq
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.Reductions.OddResidual
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.exists_k_normalizing
import Submission.Work.ThmF.ChV12.lemma2a
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.ThmF.Setup
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.ThreePoints.P3NeBot.p3_b_aux
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.involutions_commute_of_below

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.trichotomySingle` — Ch. V §2 Lemma 2(c) (and Lemma 3 a)) for a single `P`

`Work.PSU3.StageA.lemma2c` proves the `PSL(2,ℓ) / Sz(ℓ) / PSU(3,ℓ)` trichotomy for a prime-order
subgroup `P ≤ centD H t` of a group satisfying `Work.PSU3.PSU3Hyp`, whose field `B3` demands
`HasFourGroup (C_G(Q))` for *every* prime-order `Q ≤ centD H t`.  Ch. V §3 step (7) needs the
trichotomy only for the *single* subgroup `P` at hand, and in the situation of Theorem F the
hypothesis (F1) makes `B3` false at `P` itself, so `PSU3Hyp` cannot be instantiated.  The
statements below are therefore the same trichotomy (and the Ch. V §2 Lemma 3 a) input it uses)
with `PSU3Hyp` replaced by its individual fields (`Situation`, `IsSimpleGroup`,
`IsSplitRankOne`, `IsPGroup 2 Q`) and `B3` unpacked to the single instance
`HasFourGroup (C_G(P))`.  The proofs are those of `Work.PSU3.StageA.lemma2c` and
`Work.PSU3.StageA.centD_eq_centralizer_s`, with only the hypothesis references rewritten.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.PSU3.StageA

namespace Work.ThmF.Prove

theorem centD_eq_centralizer_s_single {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hsplit : IsSplitRankOne H Q t) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2)
    (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r) :
    Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) := by
  classical
  have hH : IsStronglyEmbedded H := hsplit.stronglyEmbedded
  have ht : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- The structure identity of Ch. V §2 Lemma 1 b): the pair `(s, ρ)` with `s ∈ Inv Q`,
  -- `ρ ∈ Q` and `t s t⁻¹ = ρ t ρ⁻¹` is unique.
  obtain ⟨p, hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)
  -- `(s, r⁻¹)` is such a pair, so it *is* `p`.
  have hsr' : t * s * t⁻¹ = r⁻¹ * t * (r⁻¹)⁻¹ := by
    rw [htinv, inv_inv]
    exact hsr
  have hsp : s = p.1 := by
    have h1 : (s, r⁻¹) = p := huniq (s, r⁻¹) ⟨hs, hs2, Q.inv_mem hr, hsr'⟩
    exact congrArg Prod.fst h1
  -- ## First inclusion: `V = C_D(t) ≤ D ⊓ C_G(s)`
  have hVle : Submission.Blueprint.centD H t ≤
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) := by
    refine le_inf inf_le_left ?_
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdD : d ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hd).1
    have hdC : d ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hd).2
    have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
    have hdH : d ∈ H := (Subgroup.mem_inf.mp hdD).1
    have hdNQ : d ∈ Subgroup.normalizer (Q : Set G) := hsplit.normal hdH
    have hdQ : ∀ x ∈ Q, d * x * d⁻¹ ∈ Q :=
      fun x hx => (Subgroup.mem_normalizer_iff.mp hdNQ x).mp hx
    have hds2 : orderOf (d * s * d⁻¹) = 2 := by
      rw [Work.ThmF.Bender.orderOf_conj_eq, hs2]
    -- conjugating the structure identity by `d` (which centralises `t`) gives another solution
    have hconj : t * (d * s * d⁻¹) * t⁻¹ =
        (d * r * d⁻¹)⁻¹ * t * ((d * r * d⁻¹)⁻¹)⁻¹ := by
      have hdt' : t * d = d * t := hdt.symm
      have hdtd : d * t * d⁻¹ = t := by rw [hdt]; group
      have hdinv : d⁻¹ * t = t * d⁻¹ := by
        have h := congrArg Inv.inv hdt
        exact (by simpa [mul_inv_rev, htinv] using h : t * d⁻¹ = d⁻¹ * t).symm
      rw [htinv]
      calc t * (d * s * d⁻¹) * t
          = (t * d) * s * (d⁻¹ * t) := by group
        _ = (d * t) * s * (t * d⁻¹) := by rw [hdt', hdinv]
        _ = d * (t * s * t) * d⁻¹ := by group
        _ = d * (r⁻¹ * t * r) * d⁻¹ := by rw [hsr]
        _ = (d * r⁻¹ * d⁻¹) * (d * t * d⁻¹) * (d * r * d⁻¹) := by group
        _ = (d * r * d⁻¹)⁻¹ * t * ((d * r * d⁻¹)⁻¹)⁻¹ := by
              rw [hdtd, inv_inv]
              group
    have hds : d * s * d⁻¹ = s := by
      have h1 : (d * s * d⁻¹, (d * r * d⁻¹)⁻¹) = p :=
        huniq _ ⟨hdQ s hs, hds2, Q.inv_mem (hdQ r hr), hconj⟩
      have h2 : d * s * d⁻¹ = p.1 := congrArg Prod.fst h1
      rw [h2, ← hsp]
    exact mul_inv_eq_iff_eq_mul.mp hds
  -- ## Counting: `|D ⊓ C_G(s)| ≤ |V|`
  have hcard : Nat.card (Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer ({s} : Set G) : Subgroup G) ≤
      Nat.card (Submission.Blueprint.centD H t) :=
    card_twoPoint_inf_centralizer_le_centD hH ht htH (hsplit.le hs) hs2
  exact Subgroup.eq_of_le_of_card_ge hVle hcard


theorem trichotomy_of_prime {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {P : Subgroup G} (hSitu : Situation G) (hIsSimple : IsSimpleGroup G)
    (hSpl : IsSplitRankOne H Q t) (hC4 : ChIIFourProp) (hQ2 : IsPGroup 2 Q)
    (hB3 : HasFourGroup ↥(Subgroup.centralizer (P : Set G)))
    {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q)
    (hsr : t * s * t = r⁻¹ * t * r)
    (hP : P ≤ Submission.Blueprint.centD H t) (hp : (Nat.card P).Prime) :
    let ℓ := Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))
    let C := Q ⊓ Subgroup.centralizer (P : Set G)
    (orderOf (s * t) = 3 ∧ Submission.Blueprint.IsAbelianSubgroup C ∧ Nat.card C = ℓ) ∨
    (orderOf (s * t) = 5 ∧ ¬ Submission.Blueprint.IsAbelianSubgroup C ∧ Nat.card C = ℓ ^ 2 ∧
      ∀ x ∈ C, ∀ y ∈ C, x ^ 2 = y ^ 2 → x * y⁻¹ ∈ Work.ThmF.Q0sub H) ∨
    (orderOf (s * t) = 3 ∧ Nat.card C = ℓ ^ 3 ∧
      ∃ x ∈ Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (P : Set G), x ∉ P ∧
        ∀ z ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G), x * z = z * x) := by
  classical
  haveI : IsSimpleGroup G := hIsSimple
  -- ## 0. Basic setup
  have hSit : Situation G := hSitu
  have hsplit : IsSplitRankOne H Q t := hSpl
  have hH : IsStronglyEmbedded H := hsplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := hsplit.stronglyEmbedded.2.2 t htH
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h
    simpa [pow_two] using h
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hp
    exact Nat.not_prime_one hp
  have hPD : P ≤ twoPoint H t := fun x hx => (Subgroup.mem_inf.mp (hP hx)).1
  have hPt : P ≤ Subgroup.centralizer ({t} : Set G) := fun x hx => (Subgroup.mem_inf.mp (hP hx)).2
  have hPodd : Odd (Nat.card P) := hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hPD)
  have hP4 : HasFourGroup ↥(Subgroup.centralizer (P : Set G)) := hB3
  -- `t` and `s` centralise `P`
  have htGc : t ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPt hx)
  have hsGc : s ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hA2 := centD_eq_centralizer_s_single hsplit hs hs2 hr hsr
    have hxV : x ∈ Submission.Blueprint.centD H t := hP hx
    rw [hA2] at hxV
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxV).2
  -- ## 1. `|H : Q| = |D|`, all `2`-elements of `H` lie in `Q`
  have hQHindex : (Q.subgroupOf H).index = Nat.card ↥(twoPoint H t) := by
    have hcard := Subgroup.card_mul_index (Q.subgroupOf H)
    have h1 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsplit.le).toEquiv
    rw [h1, Work.ThmF.split_card_H hsplit] at hcard
    exact Nat.mul_left_cancel Nat.card_pos hcard
  have hInvQ : ∀ u ∈ involutions (H : Set G), u ∈ Q := by
    intro u hu
    haveI : (Q.subgroupOf H).Normal := Work.ThmF.split_Q_normal_in_H hsplit
    have hu2 : orderOf (⟨u, hu.1⟩ : ↥H) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hu.2
    exact Work.ThreePoints.mem_of_orderOf_eq_two_of_odd_index
      (L := Q.subgroupOf H) (by rw [hQHindex]; exact hDodd) hu2
  -- ## 2. Involutions of `H` commute; `Q0sub H` elementary abelian
  have hDtr := Work.ThmF.Bender.DTransitiveInv hH ht2 htH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQnil : Group.IsNilpotent ↥Q := hQ2.isNilpotent
  have hcentQ : ∀ u ∈ involutions (H : Set G), u ∈ Work.ThmF.centerOf Q :=
    Work.ThmF.ChV12.prop1c hSit H Q t hsplit hDtr hQnil
  have hcommH : ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u := by
    intro u hu v hv
    have h1 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcentQ u hu)
    have h2 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcentQ v hv)
    exact h1.2 v h2.1
  have hQ0el := Work.ThmF.ChV12.Q0sub_elementary H hcommH
  have hQ0sub_le_Q : Work.ThmF.Q0sub H ≤ Q := by
    rw [Work.ThmF.Q0sub]
    refine (Subgroup.closure_le Q).mpr ?_
    intro x hx
    rw [Work.ThmF.mem_Q0_iff] at hx
    rcases hx with ⟨hxH, hx2⟩ | rfl
    · exact hInvQ x ⟨hxH, hx2⟩
    · exact Q.one_mem
  -- ## 3. `C = C_Q(P)` and `ℓ = |Inv C| + 1`
  set Gc : Subgroup G := Subgroup.centralizer (P : Set G) with hGcdef
  set C : Subgroup G := Q ⊓ Gc with hCdef
  set ℓ : ℕ := Nat.card ↥(Work.ThmF.Q0sub H ⊓ Gc) with hℓdef
  have hQ0inf_set : ((Work.ThmF.Q0sub H ⊓ Gc : Subgroup G) : Set G)
      = ({1} : Set G) ∪ involutions (C : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ0, hxGc⟩ := Subgroup.mem_inf.mp hx
      rcases eq_or_ne x 1 with rfl | hx1
      · exact Or.inl rfl
      · exact Or.inr ⟨Subgroup.mem_inf.mpr ⟨hQ0sub_le_Q hxQ0, hxGc⟩,
          (hQ0el.2.2.2 x hxQ0 hx1).2⟩
    · intro hx
      rcases hx with rfl | hx
      · exact Subgroup.mem_inf.mpr ⟨one_mem _, one_mem _⟩
      · obtain ⟨hxC, hx2⟩ := hx
        exact Subgroup.mem_inf.mpr
          ⟨Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H
              ⟨hsplit.le hxC.1, hx2⟩), hxC.2⟩
  have hℓ_eq : ℓ = (involutions (C : Set G)).ncard + 1 := by
    have hcard1 : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Gc)
        = ((Work.ThmF.Q0sub H ⊓ Gc : Subgroup G) : Set G).ncard :=
      Nat.card_coe_set_eq _
    rw [hℓdef, hcard1, hQ0inf_set,
      Set.ncard_union_eq (Set.disjoint_singleton_left.mpr (by simp [involutions]))
        (Set.finite_singleton _) (Set.toFinite _), Set.ncard_singleton]
    omega
  -- ## 4. ChIIFourProp P3 with `X = P`: the subgroup `F`, `S`, `Y` and the map `φ`
  have hP1b := (hC4 G hSit H hH t ht2 htH).1
  have hP3 := (hC4 G hSit H hH t ht2 htH).2.2.2.1
  have hX3 : 3 ≤ (fixedPts H P).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht2 htH hP
  obtain ⟨k0, hk0K, hk01, hk0N⟩ :=
    Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hP hX3 hP4 hP1b
  have hP3c := hP3 P hPne hP ⟨k0, hk0K, hk01, hk0N⟩
  dsimp only at hP3c
  rw [← hGcdef] at hP3c
  set F : Subgroup G := (Submission.Blueprint.oddResidual Gc).map Gc.subtype with hFdef
  obtain ⟨hNGP, ⟨S, hSp, hSFH, hSidx, hSNorm, hSD, hSsup⟩, ⟨hZc, hYZc⟩, hNdata⟩ := hP3c
  obtain ⟨Y, hYG, φ, hφsurj, hφker, hYbender⟩ := hYZc
  letI : Group Y := hYG
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  -- ## 5. `t`, `s`, `r` lie in `F`; `C ≤ F`; `S = C`
  have htF : t ∈ F :=
    mem_map_oddResidual_of_orderOf_eq_two_pow htGc (k := 1) (by rw [ht2, pow_one])
  have hsF : s ∈ F :=
    mem_map_oddResidual_of_orderOf_eq_two_pow hsGc (k := 1) (by rw [hs2, pow_one])
  -- `r` centralises `P`: conjugating the structure identity by `p ∈ P` and using uniqueness
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hs_comm_P : ∀ p ∈ P, p * s = s * p := by
    intro p hpP
    have hVS := centD_eq_centralizer_s_single hsplit hs hs2 hr hsr
    have hpV : p ∈ Submission.Blueprint.centD H t := hP hpP
    rw [hVS] at hpV
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hpV).2
  have ht_comm_P : ∀ p ∈ P, p * t = t * p := by
    intro p hpP
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hP hpP)).2
  have hP_le_D : P ≤ twoPoint H t := hPD
  have hP_normQ : ∀ p ∈ P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q := by
    intro p hpP q hq
    have hpH : p ∈ H := (Subgroup.mem_inf.mp (hP_le_D hpP)).1
    have hpN : p ∈ Subgroup.normalizer (Q : Set G) := hsplit.normal hpH
    exact (Subgroup.mem_normalizer_iff.mp hpN q).mp hq
  have hpair0 : (s, r⁻¹) ∈ {q : G × G | q.1 ∈ Q ∧ orderOf q.1 = 2 ∧ q.2 ∈ Q ∧
      t * q.1 * t⁻¹ = q.2 * t * q.2⁻¹} := by
    refine ⟨hs, hs2, Q.inv_mem hr, ?_⟩
    simpa [hti, inv_inv] using hsr
  have hrGc : r ∈ Gc := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have huniq := Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)
    have hpt : p * t * p⁻¹ = t := by rw [ht_comm_P p hpP]; group
    have hps : p * s * p⁻¹ = s := by rw [hs_comm_P p hpP]; group
    have hpair' : (s, (p * r * p⁻¹)⁻¹) ∈ {q : G × G | q.1 ∈ Q ∧ orderOf q.1 = 2 ∧ q.2 ∈ Q ∧
        t * q.1 * t⁻¹ = q.2 * t * q.2⁻¹} := by
      refine ⟨hs, hs2, Q.inv_mem (hP_normQ p hpP r hr), ?_⟩
      have hconj := congrArg (MulAut.conj p) hsr
      simp only [map_mul, map_inv, MulAut.conj_apply, hpt, hps] at hconj
      simpa [hti, inv_inv] using hconj
    have hEq : (s, r⁻¹) = (s, (p * r * p⁻¹)⁻¹) := huniq.unique hpair0 hpair'
    have h2 : r⁻¹ = (p * r * p⁻¹)⁻¹ := congrArg Prod.snd hEq
    have h3 : p * r * p⁻¹ = r := by
      have := congrArg Inv.inv h2
      simpa using this.symm
    calc p * r = (p * r * p⁻¹) * p := by group
      _ = r * p := by rw [h3]
  have hrF : r ∈ F :=
    mem_map_oddResidual_of_mem_isPGroup (C := Gc) hQ2 hr hrGc
  have hC_le_F : C ≤ F := by
    rw [hCdef, hFdef]
    intro x hx
    exact mem_map_oddResidual_of_mem_isPGroup (C := Gc) hQ2 hx.1 hx.2
  have hF_le_Gc : F ≤ Gc := Subgroup.map_subtype_le _
  have hC_le_H : C ≤ H := hCdef ▸ le_trans inf_le_left hsplit.le
  have hS_le_H : S ≤ H := fun x hx => (Subgroup.mem_inf.mp (hSFH hx)).2
  have hS_le_Q : S ≤ Q := by
    intro x hx
    haveI : (Q.subgroupOf H).Normal := Work.ThmF.split_Q_normal_in_H hsplit
    obtain ⟨n, hn⟩ := hSp (⟨x, hx⟩ : ↥S)
    have hxn : (⟨x, hS_le_H hx⟩ : ↥H) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg (fun g : ↥S => (g : G)) hn
      simpa using this
    exact mem_of_pow_two_eq_one_of_normal_odd_index (N := Q.subgroupOf H)
      (by rw [hQHindex]; exact hDodd) hxn
  have hS_le_C : S ≤ C := le_inf hS_le_Q ((hSFH.trans inf_le_left).trans hF_le_Gc)
  have hC_le_FH : C ≤ F ⊓ H := le_inf hC_le_F hC_le_H
  have hC2 : IsPGroup 2 ↥C := by
    intro x
    obtain ⟨n, hn⟩ := hQ2 (⟨(x : G), x.2.1⟩ : ↥Q)
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have := congrArg (fun g : ↥Q => (g : G)) hn
    simpa using this
  have hS_eq_C : S = C := by
    have hcardSS : Nat.card ↥(S.subgroupOf (F ⊓ H)) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSFH).toEquiv
    have hcardFH : Nat.card ↥(F ⊓ H)
        = Nat.card ↥S * (S.subgroupOf (F ⊓ H)).index := by
      rw [← Subgroup.card_mul_index (S.subgroupOf (F ⊓ H)), hcardSS]
    have hodd_idx : Odd (S.subgroupOf (F ⊓ H)).index :=
      Nat.not_even_iff_odd.mp (fun h => hSidx (even_iff_two_dvd.mp h))
    obtain ⟨j, hj⟩ := hC2.exists_card_eq
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    have hdvd : 2 ^ j ∣ (S.subgroupOf (F ⊓ H)).index * Nat.card ↥S := by
      have h1 : Nat.card ↥C ∣ Nat.card ↥S * (S.subgroupOf (F ⊓ H)).index := by
        rw [← hcardFH]; exact Subgroup.card_dvd_of_le hC_le_FH
      rwa [hj, mul_comm] at h1
    have hcop : Nat.Coprime (2 ^ j) (S.subgroupOf (F ⊓ H)).index :=
      (Nat.coprime_two_right.mpr hodd_idx).symm.pow_left j
    have hdvdS : 2 ^ j ∣ Nat.card ↥S := hcop.dvd_of_dvd_mul_left hdvd
    have hle : Nat.card ↥C ≤ Nat.card ↥S := by
      rw [hk] at hdvdS
      rw [hj, hk]
      exact Nat.le_of_dvd (by positivity) hdvdS
    exact Subgroup.eq_of_le_of_card_ge hS_le_C hle
  -- ## 6. The split rank-one datum in `Y = F/Z(F)` and `BenderSTProp`
  have hHF : IsStronglyEmbedded ((H ⊓ F).subgroupOf F) := by
    have hInv : involutions (Subgroup.centralizer (P : Set G) : Set G) ⊆ F := by
      intro x hx
      exact mem_map_oddResidual_of_orderOf_eq_two_pow (C := Gc) hx.1 (k := 1) (by rw [hx.2, pow_one])
    have hFN : F ≤ Subgroup.normalizer (P : Set G) :=
      hF_le_Gc.trans (Subgroup.centralizer_le_normalizer (P : Set G))
    have hPH : P ≤ Submission.Blueprint.conj (1 : G) H := by
      rw [Work.DoubleTransitivity.conj_one]; exact hPD.trans inf_le_left
    have hres := hP1b P F hX3 hInv hFN 1 hPH
    rwa [Work.DoubleTransitivity.conj_one, inf_comm] at hres
  have hkerH : φ.ker ≤ (H ⊓ F).subgroupOf F := by
    rw [hφker]
    exact center_le_of_isStronglyEmbedded hHF
  have hoddKer : Odd (Nat.card φ.ker) := by
    rw [hφker, ← hZc]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have himgSemb : IsStronglyEmbedded (((H ⊓ F).subgroupOf F).map φ) :=
    Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd φ hφsurj hoddKer hkerH hHF
  obtain ⟨Pmd, hPmdB⟩ := modelDataBorel hYbender himgSemb
  have hmod : ∃ (P : Work.Models.ModelData Y), P.B = ((H ⊓ F).subgroupOf F).map φ :=
    ⟨Pmd, hPmdB⟩
  have htF' : (⟨t, htF⟩ : ↥F) ∉ (H ⊓ F).subgroupOf F := by
    intro hmem
    exact htH (Subgroup.mem_subgroupOf.mp hmem).1
  have htF2 : orderOf (⟨t, htF⟩ : ↥F) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  have hSF_le : S.subgroupOf F ≤ (H ⊓ F).subgroupOf F := by
    intro x hx
    have hxS : (x : G) ∈ S := hx
    exact Subgroup.mem_subgroupOf.mpr ⟨hS_le_H hxS, x.2⟩
  have hSF : S ≤ F := hSFH.trans inf_le_left
  have hconjF : F.map (MulAut.conj t).toMonoidHom = F := by
    ext x
    rw [Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff]
    constructor
    · intro hx
      have hx_eq : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      rw [hx_eq]
      exact F.mul_mem (F.mul_mem htF hx) (F.inv_mem htF)
    · intro hx; exact F.mul_mem (F.mul_mem (F.inv_mem htF) hx) htF
  have htp : Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F) (⟨t, htF⟩ : ↥F)
      = (Submission.Blueprint.twoPoint H t ⊓ F).subgroupOf F := by
    rw [Work.DoubleTransitivity.Sec5.twoPoint_subgroupOf htF]
    congr 1
    change (H ⊓ F) ⊓ (H ⊓ F).map (MulAut.conj t).toMonoidHom
        = (H ⊓ H.map (MulAut.conj t).toMonoidHom) ⊓ F
    rw [Subgroup.map_inf H F (MulAut.conj t).toMonoidHom (MulAut.conj t).injective, hconjF]
    ext x; simp only [Subgroup.mem_inf]; tauto
  have hSF_sup : S.subgroupOf F ⊔ Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F)
      (⟨t, htF⟩ : ↥F) = (H ⊓ F).subgroupOf F := by
    apply Subgroup.map_injective F.subtype_injective
    rw [Subgroup.map_sup, htp, Subgroup.map_subgroupOf_eq_of_le hSF,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Submission.Blueprint.twoPoint H t ⊓ F ≤ F),
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : H ⊓ F ≤ F)]
    refine le_antisymm (sup_le (le_inf (hSFH.trans inf_le_right) (hSFH.trans inf_le_left))
      (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)) ?_
    intro x hx
    obtain ⟨hxH, hxF⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.centralizer_le_normalizer (P : Set G) (hF_le_Gc hxF)
    have hxmem : x ∈ S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G)) := by
      rw [hSsup]; exact ⟨hxH, hxN⟩
    have hnorm : Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G)
        ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf (le_trans inf_le_left inf_le_left) inf_le_right).trans hSNorm
    obtain ⟨a, haS, b, hb, hxab⟩ :=
      Commons.GroupTheory.Subgroup.mem_sup_of_le_normalizer S
        (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G)) hnorm hxmem
    have hbF : b ∈ F := by
      have hbeq : b = a⁻¹ * x := by rw [hxab]; group
      rw [hbeq]; exact F.mul_mem (F.inv_mem (hSF haS)) hxF
    rw [hxab]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haS)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hb.1, hbF⟩))
  have hSF_inf : S.subgroupOf F ⊓ Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F)
      (⟨t, htF⟩ : ↥F) = ⊥ := by
    apply Subgroup.map_injective F.subtype_injective
    rw [Subgroup.map_inf (S.subgroupOf F)
        (Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F) (⟨t, htF⟩ : ↥F))
        F.subtype F.subtype_injective, htp,
      Subgroup.map_subgroupOf_eq_of_le hSF,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Submission.Blueprint.twoPoint H t ⊓ F ≤ F),
      Subgroup.map_bot]
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    simp only [Subgroup.mem_inf] at hx
    obtain ⟨hxS, hx2, _hxF⟩ := hx
    obtain ⟨hxH, hxHt⟩ := hx2
    have hmem : x ∈ S ⊓ Submission.Blueprint.twoPoint H t :=
      Subgroup.mem_inf.mpr ⟨hxS, Subgroup.mem_inf.mpr ⟨hxH, hxHt⟩⟩
    rw [hSD, Subgroup.mem_bot] at hmem
    exact hmem
  have hSPnorm : (H ⊓ F).subgroupOf F ≤ Subgroup.normalizer ((S.subgroupOf F) : Set ↥F) := by
    have hHFN : H ⊓ F ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf inf_le_left (inf_le_right.trans (hF_le_Gc.trans
        (Subgroup.centralizer_le_normalizer (P : Set G))))).trans hSNorm
    rw [Commons.GroupTheory.Subgroup.normalizer_subgroupOf S F hSF]
    exact Subgroup.subgroupOf_mono F (le_inf hHFN inf_le_right)
  have hSp' : IsPGroup 2 ↥(S.subgroupOf F) := by
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    exact IsPGroup.of_card (n := k)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hSFH.trans inf_le_left)).toEquiv, hk])
  have hSsplit : Submission.Blueprint.IsSplitRankOne
      (((H ⊓ F).subgroupOf F).map φ) (((S.subgroupOf F).map φ)) (φ ⟨t, htF⟩) :=
    isSplitRankOneTransfer hHF htF2 htF' hZc hφsurj hφker hmod hSp'
      hSF_le hSPnorm hSF_inf hSF_sup
  -- ## 6b. The bijection `S.subgroupOf F → φ(S.subgroupOf F)` and its order preservation
  have hkerS : (S.subgroupOf F) ⊓ φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxk⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    have hd2 : orderOf x ∣ 2 ^ k := by
      have h1 : orderOf (⟨x, hxS⟩ : ↥(S.subgroupOf F)) ∣ Nat.card ↥(S.subgroupOf F) :=
        orderOf_dvd_natCard _
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv, hk] at h1
      rwa [← Subgroup.orderOf_coe (⟨x, hxS⟩ : ↥(S.subgroupOf F))] at h1
    have hd1 : orderOf x ∣ Nat.card ↥φ.ker := by
      have h1 : orderOf (⟨x, hxk⟩ : ↥φ.ker) ∣ Nat.card ↥φ.ker := orderOf_dvd_natCard _
      rwa [← Subgroup.orderOf_coe (⟨x, hxk⟩ : ↥φ.ker)] at h1
    have hcop : (2 ^ k).Coprime (Nat.card ↥φ.ker) :=
      (hoddKer.coprime_two_right).symm.pow_left k
    have hone : orderOf x = 1 := by
      have hg : orderOf x ∣ Nat.gcd (2 ^ k) (Nat.card ↥φ.ker) := Nat.dvd_gcd hd2 hd1
      rw [hcop] at hg
      exact Nat.dvd_one.mp hg
    exact orderOf_eq_one_iff.mp hone
  have hinjS : Function.Injective (fun a : ↥(S.subgroupOf F) => φ a) := by
    intro a b hab
    have hmem1 : ((a : ↥F))⁻¹ * ((b : ↥F)) ∈ (S.subgroupOf F) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ a.2) b.2
    have hmem2 : ((a : ↥F))⁻¹ * ((b : ↥F)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hab' : φ ((a : ↥F)) = φ ((b : ↥F)) := hab
      rw [map_mul, map_inv, hab', inv_mul_cancel]
    have hmem : ((a : ↥F))⁻¹ * ((b : ↥F)) ∈ (S.subgroupOf F) ⊓ φ.ker :=
      Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
    rw [hkerS, Subgroup.mem_bot] at hmem
    have hb_eq : (b : ↥F) = (a : ↥F) := by
      have h := congrArg (fun z => (a : ↥F) * z) hmem
      rw [mul_one] at h
      rw [← h]; group
    exact Subtype.ext hb_eq.symm
  have hφord : ∀ a : ↥(S.subgroupOf F), orderOf (φ a) = orderOf a := by
    intro a
    refine Nat.dvd_antisymm ?_ ?_
    · simpa only [Subgroup.orderOf_coe a] using orderOf_map_dvd φ (a : ↥F)
    · apply orderOf_dvd_iff_pow_eq_one.mpr
      have h1 : φ ((a : ↥F) ^ orderOf (φ a)) = φ 1 := by
        rw [map_pow, pow_orderOf_eq_one, map_one]
      exact hinjS (by simpa using h1)
  have hInvU : involutions (((S.subgroupOf F).map φ) : Set Y)
      = (fun a : ↥F => φ a) '' involutions ((S.subgroupOf F) : Set ↥F) := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz.1
      have h1 : orderOf (φ a) = orderOf a :=
        (hφord ⟨a, ha⟩).trans (Subgroup.orderOf_coe ⟨a, ha⟩).symm
      exact ⟨a, ⟨ha, by rw [← h1]; exact hz.2⟩, rfl⟩
    · rintro ⟨a, ⟨ha, ha2⟩, rfl⟩
      have h1 : orderOf (φ a) = orderOf a :=
        (hφord ⟨a, ha⟩).trans (Subgroup.orderOf_coe ⟨a, ha⟩).symm
      exact ⟨Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, by rw [h1, ha2]⟩
  have hInvFG : F.subtype '' involutions ((S.subgroupOf F) : Set ↥F)
      = involutions (S : Set G) := by
    ext g
    constructor
    · rintro ⟨a, ⟨ha, ha2⟩, rfl⟩
      exact ⟨Subgroup.mem_subgroupOf.mp ha, by simpa using ha2⟩
    · intro hg
      refine ⟨⟨g, hSF hg.1⟩, ⟨Subgroup.mem_subgroupOf.mpr hg.1, ?_⟩, rfl⟩
      simpa using hg.2
  have hsGQ0 : involutions (S : Set G) ⊆ (Work.ThmF.Q0sub H : Set G) := by
    rintro g ⟨hgS, hg2⟩
    exact Subgroup.subset_closure
      (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hsplit.le (hS_le_Q hgS), hg2⟩))
  have hclosU : Subgroup.closure (involutions (((S.subgroupOf F).map φ) : Set Y))
      = Subgroup.map φ (Subgroup.closure (involutions ((S.subgroupOf F) : Set ↥F))) := by
    rw [hInvU, ← MonoidHom.map_closure]
  -- ## 7. Apply `BenderSTProp`
  have hsS : s ∈ S :=
    hS_eq_C ▸ Subgroup.mem_inf.mpr ⟨hs, hsGc⟩
  have hrS : r ∈ S :=
    hS_eq_C ▸ Subgroup.mem_inf.mpr ⟨hr, hrGc⟩
  have hs2F : orderOf (⟨s, hsF⟩ : ↥F) = 2 := by rw [Subgroup.orderOf_mk]; exact hs2
  have hsrF : (⟨t, htF⟩ : ↥F) * ⟨s, hsF⟩ * ⟨t, htF⟩
      = (⟨r, hrF⟩ : ↥F)⁻¹ * ⟨t, htF⟩ * ⟨r, hrF⟩ := by
    apply Subtype.ext
    simpa using hsr
  have hodd_st : Odd (orderOf (s * t)) :=
    Work.ThmF.Bender.twoInvolutionsOdd hH (hsplit.le hs) hs2 ht2 htH
  have hsSsub : ⟨s, hsF⟩ ∈ (S.subgroupOf F) := Subgroup.mem_subgroupOf.mpr hsS
  have hrSsub : ⟨r, hrF⟩ ∈ (S.subgroupOf F) := Subgroup.mem_subgroupOf.mpr hrS
  have hsFact : (⟨s, hsF⟩ : ↥F) * ⟨s, hsF⟩ = 1 := by
    refine Subtype.ext ?_; simpa using hss
  have hs2map : orderOf (φ ⟨s, hsF⟩) = 2 := by
    have hdvd : orderOf (φ ⟨s, hsF⟩) ∣ 2 := by
      have h1 : orderOf (φ ⟨s, hsF⟩) ∣ orderOf (⟨s, hsF⟩ : ↥F) := orderOf_map_dvd φ _
      rwa [Subgroup.orderOf_mk, hs2] at h1
    have hne : φ ⟨s, hsF⟩ ≠ 1 := by
      intro h1
      have hmem : (⟨s, hsF⟩ : ↥F) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
      have hord : orderOf (⟨⟨s, hsF⟩, hmem⟩ : ↥φ.ker) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨⟨s, hsF⟩, hmem⟩ : ↥φ.ker),
          Subgroup.orderOf_mk, hs2]
      have hdvd : 2 ∣ Nat.card ↥φ.ker := by
        have h := orderOf_dvd_natCard (⟨⟨s, hsF⟩, hmem⟩ : ↥φ.ker)
        rwa [hord] at h
      exact (Nat.not_even_iff_odd.mpr hoddKer) (even_iff_two_dvd.mpr hdvd)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hcases := Work.PSU3.benderSTProp Y hYbender (((H ⊓ F).subgroupOf F).map φ) ((S.subgroupOf F).map φ)
    (φ ⟨t, htF⟩) hSsplit (φ ⟨s, hsF⟩) (φ ⟨r, hrF⟩)
    (Subgroup.mem_map.mpr ⟨⟨s, hsF⟩, hsSsub, rfl⟩)
    hs2map
    (Subgroup.mem_map.mpr ⟨⟨r, hrF⟩, hrSsub, rfl⟩)
    (by
      have := congrArg φ hsrF
      simpa only [map_mul, map_inv] using this)
  dsimp only at hcases
  -- ## 8. Transfers
  have httF : (⟨t, htF⟩ : ↥F) * ⟨t, htF⟩ = 1 := by
    refine Subtype.ext ?_; simpa using htt
  have hodd_stF : Odd (orderOf ((⟨s, hsF⟩ : ↥F) * ⟨t, htF⟩)) := by
    have h2 : orderOf ((⟨s, hsF⟩ : ↥F) * ⟨t, htF⟩) = orderOf (s * t) := by
      refine (Subgroup.orderOf_coe ((⟨s, hsF⟩ : ↥F) * ⟨t, htF⟩)).symm.trans ?_
      simp
    rw [h2]; exact hodd_st
  have horder : orderOf (s * t) = orderOf (φ ⟨s, hsF⟩ * φ ⟨t, htF⟩) := by
    have h1 := orderOfMapEq (φ := φ) (s := (⟨s, hsF⟩ : ↥F)) (t := ⟨t, htF⟩)
      (le_of_eq hφker) hsFact httF hodd_stF
    have h3 : orderOf ((⟨s, hsF⟩ : ↥F) * ⟨t, htF⟩) = orderOf (s * t) := by
      refine (Subgroup.orderOf_coe ((⟨s, hsF⟩ : ↥F) * ⟨t, htF⟩)).symm.trans ?_
      simp
    have h2 : orderOf (φ ((⟨s, hsF⟩ : ↥F) * ⟨t, htF⟩)) = orderOf (s * t) := h1.trans h3
    rw [map_mul] at h2
    exact h2.symm
  have hcardS : Nat.card ↥(((S.subgroupOf F).map φ)) = Nat.card ↥S := by
    have hker : (S.subgroupOf F) ⊓ φ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxS, hxk⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_bot]
      obtain ⟨k, hk⟩ := hSp.exists_card_eq
      have hxS' : ((x : ↥F) : G) ∈ S := Subgroup.mem_subgroupOf.mp hxS
      have hd2 : orderOf x ∣ 2 ^ k := by
        have h1 : orderOf (⟨x, hxS⟩ : ↥(S.subgroupOf F)) ∣ Nat.card ↥(S.subgroupOf F) :=
          orderOf_dvd_natCard _
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv, hk] at h1
        rwa [← Subgroup.orderOf_coe (⟨x, hxS⟩ : ↥(S.subgroupOf F))] at h1
      have hd1 : orderOf x ∣ Nat.card ↥φ.ker := by
        have h1 : orderOf (⟨x, hxk⟩ : ↥φ.ker) ∣ Nat.card ↥φ.ker := orderOf_dvd_natCard _
        rwa [← Subgroup.orderOf_coe (⟨x, hxk⟩ : ↥φ.ker)] at h1
      have hcop : (2 ^ k).Coprime (Nat.card ↥φ.ker) :=
        (hoddKer.coprime_two_right).symm.pow_left k
      have hone : orderOf x = 1 := by
        have hg : orderOf x ∣ Nat.gcd (2 ^ k) (Nat.card ↥φ.ker) := Nat.dvd_gcd hd2 hd1
        rw [hcop] at hg
        exact Nat.dvd_one.mp hg
      exact orderOf_eq_one_iff.mp hone
    have h := Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker φ hφsurj (S.subgroupOf F)
    rw [hker, Subgroup.card_bot, mul_one] at h
    rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv]
  have hcardC : Nat.card ↥C = Nat.card ↥(((S.subgroupOf F).map φ)) := by
    rw [hcardS, hS_eq_C]
  have hqℓ : (involutions ((((H ⊓ F).subgroupOf F).map φ) : Set Y)).ncard + 1 = ℓ := by
    have hUB : ((S.subgroupOf F).map φ) ≤ (((H ⊓ F).subgroupOf F).map φ) :=
      Subgroup.map_mono hSF_le
    have hnorm : (((S.subgroupOf F).map φ).subgroupOf (((H ⊓ F).subgroupOf F).map φ)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hUB]
      intro h k hh hk
      exact (Subgroup.mem_normalizer_iff.mp (hSsplit.normal hk) h).mp hh
    have hidx : Odd (((S.subgroupOf F).map φ).subgroupOf
        (((H ⊓ F).subgroupOf F).map φ)).index := by
      have hcardB := Work.ThmF.split_card_H hSsplit
      have hcardU : Nat.card ↥(((S.subgroupOf F).map φ).subgroupOf
          (((H ⊓ F).subgroupOf F).map φ)) = Nat.card ↥(((S.subgroupOf F).map φ)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
      have h1 := Subgroup.card_mul_index
        (((S.subgroupOf F).map φ).subgroupOf (((H ⊓ F).subgroupOf F).map φ))
      rw [hcardU, hcardB] at h1
      have h2 : (((S.subgroupOf F).map φ).subgroupOf
          (((H ⊓ F).subgroupOf F).map φ)).index
          = Nat.card ↥(Submission.Blueprint.twoPoint (((H ⊓ F).subgroupOf F).map φ)
              (φ ⟨t, htF⟩)) :=
        Nat.mul_left_cancel Nat.card_pos h1
      rw [h2]
      exact hSsplit.stronglyEmbedded.2.2 _ hSsplit.not_mem
    have hInv : involutions ((((H ⊓ F).subgroupOf F).map φ) : Set Y)
        = involutions (((S.subgroupOf F).map φ) : Set Y) := by
      ext z
      refine ⟨?_, fun hz => ⟨hUB hz.1, hz.2⟩⟩
      intro hz
      haveI := hnorm
      have hmem := Work.ThreePoints.mem_of_orderOf_eq_two_of_odd_index
        (L := ((S.subgroupOf F).map φ).subgroupOf (((H ⊓ F).subgroupOf F).map φ))
        (x := (⟨z, hz.1⟩ : ↥(((H ⊓ F).subgroupOf F).map φ))) hidx
        (by rw [← Subgroup.orderOf_coe (⟨z, hz.1⟩ : ↥(((H ⊓ F).subgroupOf F).map φ))]; exact hz.2)
      exact ⟨Subgroup.mem_subgroupOf.mp hmem, hz.2⟩
    have hstep : (involutions (((S.subgroupOf F).map φ) : Set Y)).ncard
        = (involutions ((S.subgroupOf F) : Set ↥F)).ncard := by
      rw [hInvU]
      symm
      refine Set.ncard_congr (fun a (_ : a ∈ involutions ((S.subgroupOf F) : Set ↥F)) => φ a)
        ?_ ?_ ?_
      · intro a ha
        exact ⟨a, ha, rfl⟩
      · intro a b ha hb hab
        have h1 := hinjS (show φ (⟨a, ha.1⟩ : ↥(S.subgroupOf F))
          = φ (⟨b, hb.1⟩ : ↥(S.subgroupOf F)) from hab)
        simpa using congrArg (fun z : ↥(S.subgroupOf F) => (z : ↥F)) h1
      · rintro b ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
    have hInv2 : (involutions (((S.subgroupOf F).map φ) : Set Y)).ncard
        = (involutions (C : Set G)).ncard := by
      rw [hstep]
      have h1 : (involutions ((S.subgroupOf F) : Set ↥F)).ncard
          = (involutions (S : Set G)).ncard := by
        rw [← hInvFG, Set.ncard_image_of_injective _ F.subtype_injective]
      rw [h1, hS_eq_C]
    rw [hInv, hInv2]
    exact hℓ_eq.symm
  have hab : IsAbelianSubgroup C ↔ IsAbelianSubgroup (((S.subgroupOf F).map φ)) := by
    rw [← hS_eq_C]
    constructor
    · intro hS_ab x hx y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      have h := hS_ab (a : G) (Subgroup.mem_subgroupOf.mp ha) (b : G)
        (Subgroup.mem_subgroupOf.mp hb)
      have h1 : (a * b : ↥F) = b * a := Subtype.ext (by simpa using h)
      calc φ a * φ b = φ (a * b) := (map_mul φ a b).symm
        _ = φ (b * a) := by rw [h1]
        _ = φ b * φ a := map_mul φ b a
    · intro hU_ab x hx y hy
      let A : ↥(S.subgroupOf F) := ⟨⟨x, hSF hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩
      let B : ↥(S.subgroupOf F) := ⟨⟨y, hSF hy⟩, Subgroup.mem_subgroupOf.mpr hy⟩
      have hxU : φ A ∈ (S.subgroupOf F).map φ := Subgroup.mem_map.mpr ⟨A, A.2, rfl⟩
      have hyU : φ B ∈ (S.subgroupOf F).map φ := Subgroup.mem_map.mpr ⟨B, B.2, rfl⟩
      have h : φ A * φ B = φ B * φ A := hU_ab (φ A) hxU (φ B) hyU
      have hAB : φ (A * B) = φ A * φ B := map_mul φ (A : ↥F) (B : ↥F)
      have hBA : φ (B * A) = φ B * φ A := map_mul φ (B : ↥F) (A : ↥F)
      have h1 : φ (A * B) = φ (B * A) := by rw [hAB, hBA]; exact h
      have h2 : A * B = B * A := hinjS h1
      exact congrArg (fun z : ↥(S.subgroupOf F) => ((z : ↥F) : G)) h2
  have heqsq : (∀ x ∈ (((S.subgroupOf F).map φ)), ∀ y ∈ (((S.subgroupOf F).map φ)),
      x ^ 2 = y ^ 2 → x * y⁻¹ ∈ Subgroup.closure (involutions ((((S.subgroupOf F).map φ) : Set Y))))
      → ∀ x ∈ C, ∀ y ∈ C, x ^ 2 = y ^ 2 → x * y⁻¹ ∈ Work.ThmF.Q0sub H := by
    intro h x hxC y hyC hxy
    rw [← hS_eq_C] at hxC hyC
    let A : ↥(S.subgroupOf F) := ⟨⟨x, hSF hxC⟩, Subgroup.mem_subgroupOf.mpr hxC⟩
    let B : ↥(S.subgroupOf F) := ⟨⟨y, hSF hyC⟩, Subgroup.mem_subgroupOf.mpr hyC⟩
    have hxU : φ A ∈ (S.subgroupOf F).map φ := Subgroup.mem_map.mpr ⟨A, A.2, rfl⟩
    have hyU : φ B ∈ (S.subgroupOf F).map φ := Subgroup.mem_map.mpr ⟨B, B.2, rfl⟩
    have hsq : (φ A) ^ 2 = (φ B) ^ 2 := by
      have h1 : (((A : ↥F) : G)) ^ 2 = (((B : ↥F) : G)) ^ 2 := hxy
      have h2 : (A : ↥F) ^ 2 = (B : ↥F) ^ 2 := Subtype.ext (by simpa using h1)
      calc (φ A) ^ 2 = φ ((A : ↥F) ^ 2) := (map_pow φ (A : ↥F) 2).symm
        _ = φ ((B : ↥F) ^ 2) := by rw [h2]
        _ = (φ B) ^ 2 := map_pow φ (B : ↥F) 2
    have hmem := h (φ A) hxU (φ B) hyU hsq
    have hmem2 : φ (A * B⁻¹) ∈ Subgroup.closure (involutions (((S.subgroupOf F).map φ) : Set Y)) := by
      have hφeq : φ A * (φ B)⁻¹ = φ ((A : ↥F) * ((B : ↥F))⁻¹) := by rw [map_mul, map_inv]
      have h2 : (A : ↥F) * ((B : ↥F))⁻¹ = (((A * B⁻¹ : ↥(S.subgroupOf F))) : ↥F) := rfl
      have hφeq' : φ A * (φ B)⁻¹ = φ (A * B⁻¹) := hφeq.trans (congrArg φ h2)
      rw [hφeq'] at hmem
      exact hmem
    rw [hclosU] at hmem2
    obtain ⟨c, hc, hφc⟩ := Subgroup.mem_map.mp hmem2
    have hclos_le : Subgroup.closure (involutions ((S.subgroupOf F) : Set ↥F)) ≤ (S.subgroupOf F) :=
      (Subgroup.closure_le _).mpr (fun a ha => ha.1)
    have hcS : c ∈ S.subgroupOf F := hclos_le hc
    have hc_eq_sub : (⟨c, hcS⟩ : ↥(S.subgroupOf F)) = A * B⁻¹ := by
      apply hinjS
      show φ c = φ (A * B⁻¹)
      exact hφc
    have herr : (((A * B⁻¹ : ↥(S.subgroupOf F))) : ↥F) ∈
        Subgroup.closure (involutions ((S.subgroupOf F) : Set ↥F)) := by
      rw [← hc_eq_sub]; exact hc
    have hout : ((((A * B⁻¹ : ↥(S.subgroupOf F))) : ↥F) : G) ∈ Work.ThmF.Q0sub H := by
      have h1 : ((((A * B⁻¹ : ↥(S.subgroupOf F))) : ↥F) : G) ∈
          Subgroup.map F.subtype (Subgroup.closure (involutions ((S.subgroupOf F) : Set ↥F))) :=
        Subgroup.mem_map.mpr ⟨((A * B⁻¹ : ↥(S.subgroupOf F)) : ↥F), herr, rfl⟩
      rw [MonoidHom.map_closure] at h1
      rw [hInvFG] at h1
      exact (Subgroup.closure_le (Work.ThmF.Q0sub H)).mpr hsGQ0 h1
    simpa using hout
  have hxcl : (∃ x ∈ Submission.Blueprint.twoPoint (((H ⊓ F).subgroupOf F).map φ) (φ ⟨t, htF⟩),
      x ≠ 1 ∧ ∀ u ∈ involutions ((((H ⊓ F).subgroupOf F).map φ) : Set Y), x * u = u * x)
      → ∃ x ∈ Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (P : Set G), x ∉ P ∧
        ∀ z ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G), x * z = z * x := by
    rintro ⟨x, hxT, hx1, hxcent⟩
    haveI : IsSimpleGroup Y := Submission.isSimpleGroup_of_isSimpleBenderGroup hYbender
    -- (A) `twoPoint B' w'` is the image of `twoPoint H t ⊓ F`
    have htw1 : Submission.Blueprint.twoPoint (((H ⊓ F).subgroupOf F).map φ) (φ ⟨t, htF⟩)
        = (Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F) ⟨t, htF⟩).map φ := by
      have hconj : Submission.Blueprint.conj (φ ⟨t, htF⟩) (((H ⊓ F).subgroupOf F).map φ)
          = (Submission.Blueprint.conj ⟨t, htF⟩ ((H ⊓ F).subgroupOf F)).map φ :=
        (Commons.GroupTheory.Subgroup.map_conj_map φ ((H ⊓ F).subgroupOf F) ⟨t, htF⟩).symm
      unfold Submission.Blueprint.twoPoint
      rw [hconj]
      exact (Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le φ ((H ⊓ F).subgroupOf F)
        (Submission.Blueprint.conj ⟨t, htF⟩ ((H ⊓ F).subgroupOf F)) hkerH).symm
    have htw : Submission.Blueprint.twoPoint (((H ⊓ F).subgroupOf F).map φ) (φ ⟨t, htF⟩)
        = (((Submission.Blueprint.twoPoint H t ⊓ F).subgroupOf F)).map φ := by
      rw [htw1, htp]
    rw [htw] at hxT
    obtain ⟨xg, hxgmem, hPhixg⟩ := Subgroup.mem_map.mp hxT
    have hxgmem' : (xg : G) ∈ Submission.Blueprint.twoPoint H t ⊓ F :=
      Subgroup.mem_subgroupOf.mp hxgmem
    have hxgD : (xg : G) ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hxgmem').1
    have hxgF : (xg : G) ∈ F := (Subgroup.mem_inf.mp hxgmem').2
    have hxgGc : (xg : G) ∈ Subgroup.centralizer (P : Set G) := hF_le_Gc hxgF
    have hxgN : (xg : G) ∈ Subgroup.normalizer (S : Set G) :=
      hSNorm (Subgroup.mem_inf.mpr ⟨hxgD.1,
        Subgroup.centralizer_le_normalizer (P : Set G) hxgGc⟩)
    -- (B) `xg` centralizes `Q0sub H ⊓ C(P)`
    have hcent : ∀ z ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G),
        (xg : G) * z = z * (xg : G) := by
      intro z hz
      have hzset : z ∈ ({1} : Set G) ∪ involutions (C : Set G) := by
        have h1 : z ∈ ((Work.ThmF.Q0sub H ⊓ Gc : Subgroup G) : Set G) := hz
        exact (Set.ext_iff.mp hQ0inf_set z).mp h1
      rcases hzset with hz1 | hzinv
      · rw [Set.mem_singleton_iff.mp hz1, mul_one, one_mul]
      · obtain ⟨hzC, hzord⟩ := hzinv
        have hzS : z ∈ S := hS_eq_C ▸ hzC
        have hzF : z ∈ F := hSF hzS
        let zg : ↥F := ⟨z, hzF⟩
        have hzgS : zg ∈ S.subgroupOf F := Subgroup.mem_subgroupOf.mpr hzS
        have hzginv : φ zg ∈ involutions ((((H ⊓ F).subgroupOf F).map φ) : Set Y) := by
          refine ⟨Subgroup.mem_map.mpr ⟨zg, hSF_le hzgS, rfl⟩, ?_⟩
          have h1 : orderOf (φ zg) = orderOf zg := by simpa using hφord ⟨zg, hzgS⟩
          have h2 : orderOf zg = 2 := by
            rw [← Subgroup.orderOf_coe zg]; exact hzord
          rw [h1, h2]
        have hxc := hxcent (φ zg) hzginv
        set c : ↥F := xg * zg * xg⁻¹ * zg⁻¹ with hcdef
        have hφc : φ c = 1 := by
          have hexp : φ c = φ xg * φ zg * (φ xg)⁻¹ * (φ zg)⁻¹ := by
            rw [hcdef]; simp only [map_mul, map_inv]
          rw [hexp, hPhixg, hxc]; group
        have hcS : c ∈ S.subgroupOf F := by
          rw [Subgroup.mem_subgroupOf]
          have h1 : (c : G) = (xg : G) * z * (xg : G)⁻¹ * z⁻¹ := by
            rw [hcdef]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rfl
          rw [h1]
          exact S.mul_mem ((Subgroup.mem_normalizer_iff.mp hxgN z).mp hzS) (S.inv_mem hzS)
        have hcbot : c ∈ (⊥ : Subgroup ↥F) := by
          have h2 : c ∈ S.subgroupOf F ⊓ φ.ker :=
            Subgroup.mem_inf.mpr ⟨hcS, MonoidHom.mem_ker.mpr hφc⟩
          rw [hkerS] at h2
          exact h2
        have hc1 : c = 1 := Subgroup.mem_bot.mp hcbot
        have hcomm : xg * zg = zg * xg := by
          calc xg * zg = (xg * zg * xg⁻¹ * zg⁻¹) * (zg * xg) := by group
            _ = 1 * (zg * xg) := by rw [hcdef.symm, hc1]
            _ = zg * xg := one_mul _
        exact congrArg (fun w : ↥F => (w : G)) hcomm
    -- (C) `xg ∉ P`
    have hnotP : (xg : G) ∉ P := by
      intro hxP
      have hgen : ((S.subgroupOf F : Set ↥F) ∪ ({⟨t, htF⟩} : Set ↥F)) ⊆
          Subgroup.centralizer ({xg} : Set ↥F) := by
        intro y hy
        rcases hy with hy | hy
        · have hyS : (y : G) ∈ S := Subgroup.mem_subgroupOf.mp hy
          have hyGc : (y : G) ∈ Gc := hS_le_C.trans inf_le_right hyS
          have hcomm : (xg : G) * (y : G) = (y : G) * (xg : G) :=
            Subgroup.mem_centralizer_iff.mp hyGc (xg : G) hxP
          exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hcomm.symm)
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          have htC : (xg : G) ∈ Subgroup.centralizer ({t} : Set G) :=
            (Subgroup.mem_inf.mp (hP hxP)).2
          have hcomm : (xg : G) * t = t * (xg : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp htC
          exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hcomm.symm)
      have hNle : Subgroup.closure ((S.subgroupOf F : Set ↥F) ∪ ({⟨t, htF⟩} : Set ↥F))
          ≤ Subgroup.centralizer ({xg} : Set ↥F) := (Subgroup.closure_le _).mpr hgen
      have hsupp : Subgroup.closure ((S.subgroupOf F : Set ↥F) ∪ ({⟨t, htF⟩} : Set ↥F))
          ⊔ φ.ker = ⊤ := by
        have hNmap : Subgroup.map φ (Subgroup.closure
            ((S.subgroupOf F : Set ↥F) ∪ ({⟨t, htF⟩} : Set ↥F))) = ⊤ := by
          rw [MonoidHom.map_closure]
          have himg : (fun y : ↥F => φ y) ''
              ((S.subgroupOf F : Set ↥F) ∪ ({⟨t, htF⟩} : Set ↥F))
              = ((S.subgroupOf F).map φ : Set Y) ∪ {φ ⟨t, htF⟩} := by
            rw [Set.image_union, Set.image_singleton, Subgroup.coe_map]
          rw [himg]
          exact Work.RankOneUniqueness.closure_Q_t_eq_top hSsplit
        have h1 := Subgroup.comap_map_eq φ (Subgroup.closure
          ((S.subgroupOf F : Set ↥F) ∪ ({⟨t, htF⟩} : Set ↥F)))
        rw [hNmap, Subgroup.comap_top] at h1
        exact h1.symm
      have hxgZ : xg ∈ Subgroup.center ↥F := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hy : y ∈ Subgroup.closure ((S.subgroupOf F : Set ↥F) ∪ ({⟨t, htF⟩} : Set ↥F))
            ⊔ φ.ker := by rw [hsupp]; exact Subgroup.mem_top y
        obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.mp hy
        have hnk' : y = n * k := hnk.symm
        have hxn : xg * n = n * xg := (Subgroup.mem_centralizer_singleton_iff.mp (hNle hn)).symm
        have hxk : xg * k = k * xg := by
          rw [hφker] at hk
          exact Subgroup.mem_center_iff.mp hk xg
        rw [hnk']
        calc (n * k) * xg = n * (k * xg) := by group
          _ = n * (xg * k) := by rw [hxk]
          _ = (n * xg) * k := by group
          _ = (xg * n) * k := by rw [hxn]
          _ = xg * (n * k) := by group
      have hxgker : xg ∈ φ.ker := by rw [hφker]; exact hxgZ
      have h1 : φ xg = 1 := MonoidHom.mem_ker.mp hxgker
      rw [hPhixg] at h1
      exact hx1 h1
    exact ⟨(xg : G), Subgroup.mem_inf.mpr ⟨hxgD, hxgGc⟩, hnotP, hcent⟩
  -- ## 9. Assemble
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨by rw [horder, h1], hab.mpr h2, by rw [hcardC, h3, hqℓ]⟩
  · exact Or.inr (Or.inl ⟨by rw [horder, h1], fun h => h2 (hab.mp h),
      by rw [hcardC, h3, hqℓ], heqsq h4⟩)
  · exact Or.inr (Or.inr ⟨by rw [horder, h1], by rw [hcardC, h2, hqℓ], hxcl h3⟩)



end Work.ThmF.Prove
