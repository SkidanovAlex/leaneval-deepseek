import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.Wiring
import Submission.Work.PSU3.StageB.three_le_fixedPts_of_centralizes
import Submission.Work.PSU3.StageB.card_centralizer_eq_cube_acyclic
import Submission.Work.PSU3.StageB.ncard_involutions_inf_H
import Submission.Work.PSU3.StageB.ncard_involutions_map_inf
import Submission.Work.PSU3.StageB.orderOf_map_sylow_mul
import Submission.Work.PSU3.StageB.t_mem_and_center_quotient
import Submission.Work.PSU3.StageB.SemiregVendored
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_P
import Submission.Work.PSU3.StageB.NotFpfStep2.isSplitRankOne_map_center
import Submission.Work.PSU3.StageB.NotFpfStep2.centD_le_centralizer_involutions_of_card_cube
import Submission.Work.PSU3.StageB.NotFpfStep2.quot_isPSU3
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.PSU3.benderSTProp
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.ThmF.ChV12.exists_k_normalizing
import Submission.Work.ThmF.ChV12.structureIdentity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false


abbrev cODD {G : Type} [Group G] (P : Subgroup G) : Subgroup G :=
  (Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (P : Set G))).map
    (Subgroup.centralizer (P : Set G)).subtype

/-- **Peterfalvi II Ch. VII §4 (2), first half** (pp. 278–280): there is `ζ₁ ∈ (V ∩ U) ∖ (P ∩ U)`
with `ζ₁ ∈ C_G(P)`, where `V = centD H t` and `U = O^{2'}(C_G(P))`, together with the source's
`ζ ∈ C_W(P)^#` such that `ζ⁻¹ ζ₁ ∈ P` (equivalently `ζ₁ ∈ ζP`).

This is the `PSU3Hyp`-bundled form of `Work.PSU3.StageB.NotFpfStep2.exists_good_zeta`.

PROOF ROUTE (the statement is TRUE; please do not declare it false):
* it is the *absolute* form of `Submission/Work/PSU3/StageB/NotFpfStep2/exists_good_zeta_rel.lean`,
  whose proof script is complete and correct; that file has no `hole` of its own but calls two
  siblings that are still hole-stubbed:
  - `NotFpfStep2.exists_mem_centD_inter_centralizerOddResidual_notMem` (`∃ v ∈ V ∩ U, v ∉ P`),
  - `NotFpfStep2.centD_inter_centralizerOddResidual_centralizes` (`V ∩ U` centralises
    `C_{Q₀}(P) = Q0sub H ⊓ C_G(P)`).
  So it suffices to prove those two statements (either inline, or as helper lemmas) and then replay
  `exists_good_zeta_rel`'s proof — which also uses the *proved*
  `NotFpfStep2.mem_mul_of_fixes_centralizer_Q0_rel` (`v ∈ P·W` by Galois theory) and then extracts
  `ζ = w` from `v ∈ P·W` using `P` abelian and `v ∈ C_G(P)`.
* For `∃ v ∈ V ∩ U, v ∉ P`, the literature route is Peterfalvi II Ch. VII §4 (2): the structure of
  `U/Z(U) ≅ PSU(3, ℓ)` gives `(V ∩ U)/(P ∩ U) ≅ centD B̄ w̄` of order `(ℓ+1)/gcd(ℓ+1,3) ≠ 1`
  (as `ℓ = 2^{n'} ≥ 4`), matching the *model* statement
  `Work.PSU3.StageA.centD_le_W_psu3Model` / `Work.PSU3.Model.psu3_datum`; the available proved
  tools are `Work.PSU3.StageB.NotFpfStep2.isSplitRankOne_map_center` (the datum in
  `Y = F/Z(F)`), `Work.PSU3.StageB.NotFpfStep2.relative_quot_isPSU3`-style structure, and the
  relative Ch. V §2 Lemma 2 c) `Work.PSU3.StageB.NotFpfStep2.lemma2cHig_rel` (proved, complete,
  in `NotFpfStep2/rel_tools.lean`) together with `Rel/*` and `NotFpfStep2/*_rel` siblings.
* DO NOT be deterred by the "vacuous over `PSU3Hyp`" audit note: the only in-workspace route to a
  contradiction from these hypotheses goes through the hole-stubbed
  `Work.PSU3.StageA.centD_le_W_of_PSU3Hyp`, which is unusable in a hole-free proof. The statement
  carries the genuine content of Peterfalvi II Ch. VII §4 (2). -/
theorem exists_good_zeta_PSU3 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hQ3 : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) (hW : Work.ThmF.W H t ≠ ⊥)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    (hPne : P ≠ ⊥) {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y)
    (hZV : (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
      (Work.PSU3.StageB.centralizerOddResidual P).subtype ≤ Submission.Blueprint.centD H t) :
    ∃ ζ₁ ∈ Submission.Blueprint.centD H t,
      ζ₁ ∈ Work.PSU3.StageB.centralizerOddResidual P ∧
      (∀ p ∈ P, p⁻¹ * ζ₁ * p = ζ₁) ∧ ζ₁ ∉ P ∧
      ∃ ζ ∈ Work.ThmF.W H t, ζ ≠ 1 ∧ (∀ p ∈ P, p⁻¹ * ζ * p = ζ) ∧ ζ⁻¹ * ζ₁ ∈ P := by
  classical
  -- ## 0.  Ambient data
  have hH : IsStronglyEmbedded H := hS.split.stronglyEmbedded
  have ht2 : orderOf t = 2 := hS.split.invol
  have htH : t ∉ H := hS.split.not_mem
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hS.split
  have hy1 : y ≠ 1 := fun h1 => hy0 (by rw [h1]; exact (Work.ThmF.Q0sub H).one_mem)
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  -- ## 1.  `orderOf (s * t) = 3` (case (c) of Ch. VI §1, from `W ≠ ⊥`)
  have hst3 : orderOf (s * t) = 3 :=
    (Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hW).2.1
  -- ## 2.  The `ChIIFourProp` P3 clause at `X = P`
  have hP1b := (hC4 G hS.situation H hH t ht2 htH).1
  have hP3 := (hC4 G hS.situation H hH t ht2 htH).2.2.2.1
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard :=
    Work.PSU3.StageB.three_le_fixedPts_of_centralizes hS.split
      (fun z hz => (Subgroup.mem_inf.mp (hPV hz)).1) hyQ hy1 hyc
  have hP4 : Submission.Blueprint.HasFourGroup ↥(Subgroup.centralizer (P : Set G)) :=
    hS.B3 P hPV hPp
  obtain ⟨k0, hk0K, hk01, hk0N⟩ :=
    Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hPV hX3 hP4 hP1b
  have hP3c := hP3 P hPne hPV ⟨k0, hk0K, hk01, hk0N⟩
  dsimp only at hP3c
  obtain ⟨-, ⟨S, hSp, hSFH, hSidx, hSNorm, hSD, hSsup⟩, ⟨hZc, hYZc⟩, -⟩ := hP3c
  obtain ⟨Y, hYG, φ, hφsurj, hφker, hYbender⟩ := hYZc
  letI : Group Y := hYG
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  -- ## 3.  notation
  have htF : t ∈ ((cODD P)) :=
    (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).1
  have hF_le_Gc : ((cODD P)) ≤
      Subgroup.centralizer (P : Set G) := Subgroup.map_subtype_le _
  -- ## 4.  `Z(U) ≤ P`
  have hZPsub : Subgroup.center ↥((cODD P)) ≤ P.subgroupOf ((cODD P)) :=
    Work.PSU3.StageB.NotFpfStep2.center_le_P hS hC4 hHig hQ3 hW hPV hPp hyQ hy0 hyc hZV
  have hZP : (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype ≤ P := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_subgroupOf.mp (hZPsub hu)
  -- ## 5.  `s` and `r` centralise `P`, hence lie in `((cODD P))`
  have hVs := Work.PSU3.StageA.centD_eq_centralizer_s hS hs hs2 hr hsr
  have hsGc : s ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpV : p ∈ Submission.Blueprint.centD H t := hPV hp
    rw [hVs] at hpV
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hpV).2
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h
    simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hs_comm_P : ∀ p ∈ P, p * s = s * p := by
    intro p hp
    have hpV : p ∈ Submission.Blueprint.centD H t := hPV hp
    rw [hVs] at hpV
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hpV).2
  have ht_comm_P : ∀ p ∈ P, p * t = t * p := by
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hPV hp)).2
  have hP_normQ : ∀ p ∈ P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q := by
    intro p hp q hq
    have hpH : p ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hPV hp)).1).1
    have hpN : p ∈ Subgroup.normalizer (Q : Set G) := hsplit.normal hpH
    exact (Subgroup.mem_normalizer_iff.mp hpN q).mp hq
  have hpair0 : (s, r⁻¹) ∈ {q : G × G | q.1 ∈ Q ∧ orderOf q.1 = 2 ∧ q.2 ∈ Q ∧
      t * q.1 * t⁻¹ = q.2 * t * q.2⁻¹} := by
    refine ⟨hs, hs2, Q.inv_mem hr, ?_⟩
    simpa [hti, inv_inv] using hsr
  have hrGc : r ∈ Subgroup.centralizer (P : Set G) := by
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
  have hsF : s ∈ ((cODD P)) :=
    Work.PSU3.StageA.mem_map_oddResidual_of_mem_isPGroup (C := Subgroup.centralizer (P : Set G))
      hS.two hs hsGc
  have hrF : r ∈ ((cODD P)) :=
    Work.PSU3.StageA.mem_map_oddResidual_of_mem_isPGroup (C := Subgroup.centralizer (P : Set G))
      hS.two hr hrGc
  -- ## 6.  the split rank-one datum in `Y = ((cODD P))/Z(((cODD P)))`
  have hYX : Submission.Blueprint.IsSplitRankOne (((H ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ) (((Q ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ) (φ ⟨t, htF⟩) :=
    Work.PSU3.StageB.NotFpfStep2.isSplitRankOne_map_center hS hC4 hPV hPp hφsurj hφker hYbender
  -- ## 7.  the cardinality `|U_Y| = (#Inv B_Y + 1)^3`
  have hQCF : Q ⊓ ((cODD P)) = Q ⊓ Subgroup.centralizer (P : Set G) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact ⟨(Subgroup.mem_inf.mp hx).1, hF_le_Gc (Subgroup.mem_inf.mp hx).2⟩
    · intro x hx
      obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
      exact ⟨hxQ, Work.PSU3.StageA.mem_map_oddResidual_of_mem_isPGroup
        (C := Subgroup.centralizer (P : Set G)) hS.two hxQ hxC⟩
  have hZS : Q ⊓ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype = ⊥ :=
    Work.PSU3.StageB.inf_center_centralizerOddResidual_eq_bot hS hPV hZP le_rfl
  have hker_bot : ((Q ⊓ ((cODD P))).subgroupOf ((cODD P))) ⊓ φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxk⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    have hxG : ((x : ↥((cODD P))) : G) ∈ Q := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxQ)).1
    have hxZ : ((x : ↥((cODD P))) : G) ∈ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype := by
      rw [hφker] at hxk
      exact Subgroup.mem_map.mpr ⟨x, hxk, rfl⟩
    have hmem : ((x : ↥((cODD P))) : G) ∈ Q ⊓ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype :=
      Subgroup.mem_inf.mpr ⟨hxG, hxZ⟩
    rw [hZS, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hinj : Function.Injective (fun a : ↥((Q ⊓ ((cODD P))).subgroupOf ((cODD P))) => φ (a : ↥((cODD P)))) := by
    intro a b hab
    have hmem1 : ((a : ↥((cODD P))))⁻¹ * ((b : ↥((cODD P)))) ∈ (Q ⊓ ((cODD P))).subgroupOf ((cODD P)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ a.2) b.2
    have hmem2 : ((a : ↥((cODD P))))⁻¹ * ((b : ↥((cODD P)))) ∈ φ.ker :=
      MonoidHom.mem_ker.mpr (by
        rw [map_mul, map_inv, show φ (a : ↥((cODD P))) = φ (b : ↥((cODD P))) from hab]
        exact inv_mul_cancel _)
    have hmem : ((a : ↥((cODD P))))⁻¹ * ((b : ↥((cODD P)))) ∈ ((Q ⊓ ((cODD P))).subgroupOf ((cODD P))) ⊓ φ.ker :=
      Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
    rw [hker_bot, Subgroup.mem_bot] at hmem
    have hba : (b : ↥((cODD P))) = (a : ↥((cODD P))) := by
      have h := congrArg (fun z => (a : ↥((cODD P))) * z) hmem
      rw [mul_one] at h
      rw [← h]; group
    exact Subtype.ext hba.symm
  have hcardU : Nat.card ↥(((Q ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ) = Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) := by
    change Nat.card ↥(((Q ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ) = _
    have h := Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker φ hφsurj
      ((Q ⊓ ((cODD P))).subgroupOf ((cODD P)))
    rw [hker_bot, Subgroup.card_bot, mul_one] at h
    rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hQCF]
  have hcardC : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G))
      = (Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))) ^ 3 :=
    Work.PSU3.StageB.card_centralizer_eq_cube_acyclic hS hC4 Work.PSU3.benderSTProp
      hs hs2 hr hsr hst3 hPV hPp hyQ hy0 hyc
  have hinv_raw : (Submission.Blueprint.involutions ((((cODD P)) ⊓ H : Subgroup G) : Set G)).ncard + 1
      = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) :=
    Work.PSU3.StageB.ncard_involutions_inf_H hS hC4 hPV
  have hinvmap : (Submission.Blueprint.involutions (((H ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ : Set Y)).ncard
      = (Submission.Blueprint.involutions ((((cODD P)) ⊓ H : Subgroup G) : Set G)).ncard :=
    Work.PSU3.StageB.ncard_involutions_map_inf hS hPV hZP hφker
  have hinv : (Submission.Blueprint.involutions (((H ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ : Set Y)).ncard + 1
      = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := by
    rw [hinvmap]; exact hinv_raw
  have hcard3 : Nat.card ↥(((Q ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ)
      = ((Submission.Blueprint.involutions (((H ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ : Set Y)).ncard + 1) ^ 3 := by
    rw [hcardU, hcardC, ← hinv]
  -- ## 8.  `ℓ ≥ 4`
  obtain ⟨n', hn'2, hn'cardL, -⟩ :=
    Work.PSU3.StageB.NotFpfStep2.quot_isPSU3 hS hC4 hHig hQ3 hW hPV hPp hPne hyQ hy0 hyc hZV
  have hLge : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := by
    rw [hn'cardL]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn'2
  -- ## 9.  the trichotomy of `BenderSTProp` in `Y`
  have hsU : φ ⟨s, hsF⟩ ∈ ((Q ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ :=
    Subgroup.mem_map.mpr ⟨⟨s, hsF⟩, Subgroup.mem_subgroupOf.mpr ⟨hs, hsF⟩, rfl⟩
  have hrU : φ ⟨r, hrF⟩ ∈ ((Q ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ :=
    Subgroup.mem_map.mpr ⟨⟨r, hrF⟩, Subgroup.mem_subgroupOf.mpr ⟨hr, hrF⟩, rfl⟩
  have hs2map : orderOf (φ ⟨s, hsF⟩) = 2 := by
    have hsF2 : (⟨s, hsF⟩ : ↥((cODD P))) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      have h := pow_orderOf_eq_one s
      rw [hs2] at h
      simpa [pow_two] using h
    have hsq : (φ ⟨s, hsF⟩) ^ 2 = 1 := by rw [← map_pow, hsF2, map_one]
    have hne : φ ⟨s, hsF⟩ ≠ 1 := by
      intro h1
      have hk : (⟨s, hsF⟩ : ↥((cODD P))) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
      rw [hφker] at hk
      have hsZ : s ∈ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype := Subgroup.mem_map.mpr ⟨_, hk, rfl⟩
      have hmem : s ∈ Q ⊓ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype := Subgroup.mem_inf.mpr ⟨hs, hsZ⟩
      rw [hZS, Subgroup.mem_bot] at hmem
      rw [hmem] at hs2
      simp at hs2
    have hdvd : orderOf (φ ⟨s, hsF⟩) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hsrF : (⟨t, htF⟩ : ↥((cODD P))) * ⟨s, hsF⟩ * ⟨t, htF⟩
      = (⟨r, hrF⟩ : ↥((cODD P)))⁻¹ * ⟨t, htF⟩ * ⟨r, hrF⟩ := by
    apply Subtype.ext
    simpa using hsr
  have hsrY : φ ⟨t, htF⟩ * φ ⟨s, hsF⟩ * φ ⟨t, htF⟩ = (φ ⟨r, hrF⟩)⁻¹ * φ ⟨t, htF⟩ * φ ⟨r, hrF⟩ := by
    have := congrArg φ hsrF
    simpa only [map_mul, map_inv] using this
  have hordSY : orderOf (φ ⟨s, hsF⟩ * φ ⟨t, htF⟩) = orderOf (s * t) :=
    Work.PSU3.StageB.orderOf_map_sylow_mul hS hs hs2 (le_of_eq hφker)
      ⟨s, hsF⟩ ⟨t, htF⟩ rfl rfl
  have hcase := Work.PSU3.benderSTProp Y hYbender (((H ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ) (((Q ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ) (φ ⟨t, htF⟩) hYX
    (φ ⟨s, hsF⟩) (φ ⟨r, hrF⟩) hsU hs2map hrU hsrY
  dsimp only at hcase
  have hxY : ∃ x ∈ Submission.Blueprint.twoPoint ((((H ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ)) (φ ⟨t, htF⟩), x ≠ 1 ∧
      ∀ u ∈ Submission.Blueprint.involutions (((H ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ : Set Y), x * u = u * x := by
    rcases hcase with ⟨-, -, hcard⟩ | ⟨h1, -, -, -⟩ | ⟨-, -, h3⟩
    · exfalso
      have h1' : Nat.card ↥(((Q ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ)
          = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := hcard.trans hinv
      have h2' : Nat.card ↥(((Q ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ)
          = (Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))) ^ 3 := by
        rw [hcard3, hinv]
      have hcube : (Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))) ^ 3
          = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := by
        rw [← h2', h1']
      have hcube2 : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))
            * (Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))
            * Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)))
          = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) * 1 := by
        calc Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))
              * (Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))
              * Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)))
            = (Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))) ^ 3 := by ring
          _ = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := hcube
          _ = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) * 1 :=
              (mul_one _).symm
      have hsq : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))
          * Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) = 1 :=
        Nat.mul_left_cancel (by omega) hcube2
      have hle1 : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) ≤ 1 :=
        Nat.le_of_dvd (by norm_num) ⟨_, hsq.symm⟩
      omega
    · exfalso
      have h3 : orderOf (φ ⟨s, hsF⟩ * φ ⟨t, htF⟩) = 3 := by rw [hordSY, hst3]
      rw [h3] at h1
      exact absurd h1 (by norm_num)
    · exact h3
  -- ## 10.  the witness lifted to `D ⊓ ((cODD P))`
  obtain ⟨xbar, hxbarT, hxbar1, hxbarcent⟩ := hxY
  -- (a)  `twoPoint B_Y w_Y` is the image of `twoPoint H t ⊓ ((cODD P))`
  have hHF : IsStronglyEmbedded ((H ⊓ ((cODD P))).subgroupOf ((cODD P))) := by
    have hInv : Submission.Blueprint.involutions (Subgroup.centralizer (P : Set G) : Set G)
        ⊆ ((cODD P)) := by
      intro x hx
      exact Work.PSU3.StageA.mem_map_oddResidual_of_orderOf_eq_two_pow
        (C := Subgroup.centralizer (P : Set G)) hx.1 (k := 1) (by rw [hx.2, pow_one])
    have hFN : ((cODD P)) ≤ Subgroup.normalizer (P : Set G) :=
      hF_le_Gc.trans (Subgroup.centralizer_le_normalizer (P : Set G))
    have hPH : P ≤ Submission.Blueprint.conj (1 : G) H := by
      rw [Work.DoubleTransitivity.conj_one]
      exact fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hPV hx)).1).1
    have hres := hP1b P ((cODD P)) hX3 hInv hFN 1 hPH
    rwa [Work.DoubleTransitivity.conj_one, inf_comm] at hres
  have hkerH : φ.ker ≤ (H ⊓ ((cODD P))).subgroupOf ((cODD P)) := by
    rw [hφker]
    exact Work.PSU3.StageA.center_le_of_isStronglyEmbedded hHF
  have hconjF : ((cODD P)).map (MulAut.conj t).toMonoidHom = ((cODD P)) := by
    ext x
    rw [Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff]
    constructor
    · intro hx
      have hx_eq : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      rw [hx_eq]
      exact ((cODD P)).mul_mem (((cODD P)).mul_mem htF hx) (((cODD P)).inv_mem htF)
    · intro hx; exact ((cODD P)).mul_mem (((cODD P)).mul_mem (((cODD P)).inv_mem htF) hx) htF
  have htp : Submission.Blueprint.twoPoint ((H ⊓ ((cODD P))).subgroupOf ((cODD P))) (⟨t, htF⟩ : ↥((cODD P)))
      = (Submission.Blueprint.twoPoint H t ⊓ ((cODD P))).subgroupOf ((cODD P)) := by
    rw [Work.DoubleTransitivity.Sec5.twoPoint_subgroupOf htF]
    congr 1
    change (H ⊓ ((cODD P))) ⊓ (H ⊓ ((cODD P))).map (MulAut.conj t).toMonoidHom
        = (H ⊓ H.map (MulAut.conj t).toMonoidHom) ⊓ ((cODD P))
    rw [Subgroup.map_inf H ((cODD P)) (MulAut.conj t).toMonoidHom (MulAut.conj t).injective, hconjF]
    ext x; simp only [Subgroup.mem_inf]; tauto
  have htw1 : Submission.Blueprint.twoPoint ((((H ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ)) (φ ⟨t, htF⟩)
      = (Submission.Blueprint.twoPoint ((H ⊓ ((cODD P))).subgroupOf ((cODD P))) (⟨t, htF⟩ : ↥((cODD P)))).map φ := by
    have hconj : Submission.Blueprint.conj (φ ⟨t, htF⟩) (((H ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ)
        = (Submission.Blueprint.conj ⟨t, htF⟩ ((H ⊓ ((cODD P))).subgroupOf ((cODD P)))).map φ :=
      (Commons.GroupTheory.Subgroup.map_conj_map φ ((H ⊓ ((cODD P))).subgroupOf ((cODD P))) ⟨t, htF⟩).symm
    unfold Submission.Blueprint.twoPoint
    rw [hconj]
    exact (Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le φ ((H ⊓ ((cODD P))).subgroupOf ((cODD P)))
      (Submission.Blueprint.conj ⟨t, htF⟩ ((H ⊓ ((cODD P))).subgroupOf ((cODD P)))) hkerH).symm
  have htw : Submission.Blueprint.twoPoint ((((H ⊓ ((cODD P))).subgroupOf ((cODD P))).map φ)) (φ ⟨t, htF⟩)
      = (((Submission.Blueprint.twoPoint H t ⊓ ((cODD P))).subgroupOf ((cODD P)))).map φ := by
    rw [htw1, htp]
  rw [htw] at hxbarT
  obtain ⟨xg, hxgmem, hPhixg⟩ := Subgroup.mem_map.mp hxbarT
  have hxgmem' : (xg : G) ∈ Submission.Blueprint.twoPoint H t ⊓ ((cODD P)) :=
    Subgroup.mem_subgroupOf.mp hxgmem
  have hxgD : (xg : G) ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hxgmem').1
  have hxgF : (xg : G) ∈ ((cODD P)) := (Subgroup.mem_inf.mp hxgmem').2
  have hxgGc : (xg : G) ∈ Subgroup.centralizer (P : Set G) := hF_le_Gc hxgF
  -- (b)  `xg` centralises `Q0sub H ⊓ C_G(P)`
  have hQ0s := Work.PSU3.StageA.V_Q0sub_structure hS hC4
  have hQ0_le_Q : Work.ThmF.Q0sub H ≤ Q := Work.PSU3.StageA.Q0sub_le_Q hsplit
  have hcent : ∀ z ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G),
      (xg : G) * z = z * (xg : G) := by
    intro z hz
    obtain ⟨hzQ0, hzGc⟩ := Subgroup.mem_inf.mp hz
    by_cases hz1 : z = 1
    · rw [hz1, mul_one, one_mul]
    · have hzinv : z ∈ Submission.Blueprint.involutions (H : Set G) := hQ0s.2.2.2 z hzQ0 hz1
      have hzF : z ∈ ((cODD P)) := Work.PSU3.StageA.mem_map_oddResidual_of_mem_isPGroup
        (C := Subgroup.centralizer (P : Set G)) hS.two (hQ0_le_Q hzQ0) hzGc
      let zg : ↥((cODD P)) := ⟨z, hzF⟩
      have hzinvY : φ zg ∈ Submission.Blueprint.involutions (((H ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ : Set Y) := by
        refine ⟨Subgroup.mem_map.mpr ⟨zg, Subgroup.mem_subgroupOf.mpr ⟨hzinv.1, hzF⟩, rfl⟩, ?_⟩
        have hsq : (φ zg) ^ 2 = 1 := by
          have hz2 : (zg : ↥((cODD P))) ^ 2 = 1 := by
            apply Subtype.ext
            simp only [Subgroup.coe_pow, Subgroup.coe_one]
            have h := pow_orderOf_eq_one z
            rw [hzinv.2] at h
            simpa [pow_two] using h
          rw [← map_pow, hz2, map_one]
        have hne : φ zg ≠ 1 := by
          intro h1
          have hk : zg ∈ φ.ker := MonoidHom.mem_ker.mpr h1
          rw [hφker] at hk
          have hzZ : z ∈ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype := Subgroup.mem_map.mpr ⟨zg, hk, rfl⟩
          have hmem : z ∈ Q ⊓ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype :=
            Subgroup.mem_inf.mpr ⟨hQ0_le_Q hzQ0, hzZ⟩
          rw [hZS, Subgroup.mem_bot] at hmem
          exact hz1 hmem
        have hdvd : orderOf (φ zg) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hne
        · exact h
      have hxc := hxbarcent (φ zg) hzinvY
      set c : ↥((cODD P)) := xg * zg * xg⁻¹ * zg⁻¹ with hcdef
      have hφc : φ c = 1 := by
        have hexp : φ c = φ xg * φ zg * (φ xg)⁻¹ * (φ zg)⁻¹ := by
          rw [hcdef]; simp only [map_mul, map_inv]
        rw [hexp, hPhixg, hxc]; group
      have hcbot : c = 1 := by
        have hk : c ∈ φ.ker := MonoidHom.mem_ker.mpr hφc
        rw [hφker] at hk
        have hcZ : ((c : ↥((cODD P))) : G) ∈ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype :=
          Subgroup.mem_map.mpr ⟨c, hk, rfl⟩
        have hcQ0 : ((c : ↥((cODD P))) : G) ∈ Work.ThmF.Q0sub H := by
          have h1 : ((c : ↥((cODD P))) : G) = (xg : G) * z * (xg : G)⁻¹ * z⁻¹ := by
            rw [hcdef]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rfl
          rw [h1]
          exact (Work.ThmF.Q0sub H).mul_mem
            (hQ0s.2.2.1 (xg : G) hxgD.1 z hzQ0) ((Work.ThmF.Q0sub H).inv_mem hzQ0)
        have hcQ : ((c : ↥((cODD P))) : G) ∈ Q := hQ0_le_Q hcQ0
        have hmem : ((c : ↥((cODD P))) : G) ∈ Q ⊓ (Subgroup.center ↥((cODD P))).map ((cODD P)).subtype :=
          Subgroup.mem_inf.mpr ⟨hcQ, hcZ⟩
        rw [hZS, Subgroup.mem_bot] at hmem
        exact Subtype.ext hmem
      have hcomm : xg * zg = zg * xg := by
        calc xg * zg = (xg * zg * xg⁻¹ * zg⁻¹) * (zg * xg) := by group
          _ = 1 * (zg * xg) := by rw [hcdef.symm, hcbot]
          _ = zg * xg := one_mul _
      exact congrArg (fun w : ↥((cODD P)) => (w : G)) hcomm
  -- (c)  `xg ∉ P`
  have hnotP : (xg : G) ∉ P := by
    intro hxP
    have hxgV : (xg : G) ∈ Submission.Blueprint.centD H t := hPV hxP
    have hgen : ((Q ⊓ ((cODD P))).subgroupOf ((cODD P)) : Set ↥((cODD P))) ∪ ({⟨t, htF⟩} : Set ↥((cODD P))) ⊆
        Subgroup.centralizer ({xg} : Set ↥((cODD P))) := by
      intro y hy
      rcases hy with hy | hy
      · have hyC : ((y : ↥((cODD P))) : G) ∈ Subgroup.centralizer (P : Set G) :=
          hF_le_Gc (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2
        have hcomm : (xg : G) * (y : G) = (y : G) * (xg : G) :=
          Subgroup.mem_centralizer_iff.mp hyC (xg : G) hxP
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hcomm.symm)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        have htC : (xg : G) ∈ Subgroup.centralizer ({t} : Set G) :=
          (Subgroup.mem_inf.mp hxgV).2
        have hcomm : (xg : G) * t = t * (xg : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp htC
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hcomm.symm)
    have hNle : Subgroup.closure (((Q ⊓ ((cODD P))).subgroupOf ((cODD P)) : Set ↥((cODD P))) ∪ ({⟨t, htF⟩} : Set ↥((cODD P))))
        ≤ Subgroup.centralizer ({xg} : Set ↥((cODD P))) := (Subgroup.closure_le _).mpr hgen
    have hsupp : Subgroup.closure (((Q ⊓ ((cODD P))).subgroupOf ((cODD P)) : Set ↥((cODD P))) ∪ ({⟨t, htF⟩} : Set ↥((cODD P))))
        ⊔ φ.ker = ⊤ := by
      have hNmap : Subgroup.map φ (Subgroup.closure
          (((Q ⊓ ((cODD P))).subgroupOf ((cODD P)) : Set ↥((cODD P))) ∪ ({⟨t, htF⟩} : Set ↥((cODD P))))) = ⊤ := by
        rw [MonoidHom.map_closure]
        have himg : (fun y : ↥((cODD P)) => φ y) ''
            (((Q ⊓ ((cODD P))).subgroupOf ((cODD P)) : Set ↥((cODD P))) ∪ ({⟨t, htF⟩} : Set ↥((cODD P))))
            = (((Q ⊓ ((cODD P))).subgroupOf (((cODD P)))).map φ : Set Y) ∪ {φ ⟨t, htF⟩} := by
          rw [Set.image_union, Set.image_singleton, Subgroup.coe_map]
        rw [himg]
        haveI : IsSimpleGroup Y := Submission.isSimpleGroup_of_isSimpleBenderGroup hYbender
        exact Work.RankOneUniqueness.closure_Q_t_eq_top hYX
      have h1 := Subgroup.comap_map_eq φ (Subgroup.closure
        (((Q ⊓ ((cODD P))).subgroupOf ((cODD P)) : Set ↥((cODD P))) ∪ ({⟨t, htF⟩} : Set ↥((cODD P)))))
      rw [hNmap, Subgroup.comap_top] at h1
      exact h1.symm
    have hxgZ : xg ∈ Subgroup.center ↥((cODD P)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz : z ∈ Subgroup.closure (((Q ⊓ ((cODD P))).subgroupOf ((cODD P)) : Set ↥((cODD P))) ∪ ({⟨t, htF⟩} : Set ↥((cODD P))))
          ⊔ φ.ker := by rw [hsupp]; exact Subgroup.mem_top z
      obtain ⟨a, ha, bb, hbb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hz
      have hab' : z = a * bb := hab.symm
      have hxa : xg * a = a * xg :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hNle ha)).symm
      have hxb : xg * bb = bb * xg := by
        rw [hφker] at hbb
        exact Subgroup.mem_center_iff.mp hbb xg
      rw [hab']
      calc (a * bb) * xg = a * (bb * xg) := by group
        _ = a * (xg * bb) := by rw [hxb]
        _ = (a * xg) * bb := by group
        _ = (xg * a) * bb := by rw [hxa]
        _ = xg * (a * bb) := by group
    have hxgker : xg ∈ φ.ker := by rw [hφker]; exact hxgZ
    have h1 : φ xg = 1 := MonoidHom.mem_ker.mp hxgker
    rw [hPhixg] at h1
    exact hxbar1 h1
  -- ## 11.  `xg ∈ V` (the `ChIIFourProp` Prop. 2 (a) argument)
  have hxV : (xg : G) ∈ Submission.Blueprint.centD H t := by
    obtain ⟨u, huInv, huV⟩ := (hC4 G hS.situation H hH t ht2 htH).2.1
    have huQ0 : u ∈ Work.ThmF.Q0sub H :=
      Subgroup.subset_closure (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨huInv.1, huInv.2⟩))
    have huCP : u ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : p ∈ Submission.Blueprint.twoPoint H t
          ⊓ Subgroup.centralizer ({u} : Set G) := huV ▸ hPV hp
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hp').2
    have hxu : (xg : G) * u = u * (xg : G) := hcent u ⟨huQ0, huCP⟩
    rw [huV]
    exact Subgroup.mem_inf.mpr ⟨hxgD, Subgroup.mem_centralizer_singleton_iff.mpr hxu⟩
  -- ## 12.  the Galois step:  `xg ∈ P · W`
  have hsem : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H :=
    Work.PSU3.StageA.V_caseC_W_semireg hS hC4 hHig hQ3
  have hPy : ∀ p ∈ P, p * y = y * p := by
    intro p hp
    have h := hyc p hp
    calc p * y = p * (p⁻¹ * y * p) := by rw [h]
      _ = y * p := by group
  have hWy : ∀ w ∈ Work.ThmF.W H t, w * y = y * w → w = 1 := by
    intro w hw hwy
    by_contra hw1
    exact hy0 (hsem w hw hw1 y hyQ hwy)
  have hPW : P ⊓ Work.ThmF.W H t = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro p hp
    rw [Subgroup.mem_inf] at hp
    rw [Subgroup.mem_bot]
    by_contra hp1
    exact hp1 (hWy p hp.2 (hPy p hp.1))
  have hgalois := Work.PSU3.StageB.NotFpfStep2.mem_mul_of_fixes_centralizer_Q0 hS hC4 hPV hPW hW
  have hfix : ∀ z ∈ Work.ThmF.Q0sub H, z ∈ Subgroup.centralizer (P : Set G) →
      (xg : G) * z = z * (xg : G) := fun z hz hzc => hcent z ⟨hz, hzc⟩
  obtain ⟨p, hpP, w, hwW, hpw⟩ := Set.mem_mul.mp (hgalois (xg : G) hxV hfix)
  -- ## 13.  `w` is the source's `ζ`
  have hxw : (xg : G) = p * w := hpw.symm
  have hweq : w = p⁻¹ * (xg : G) := by rw [hxw]; group
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a :=
    Work.PSU3.StageB.NotFpfStep2.comm_of_prime_card hPp
  have hwp : w * p = p * w := by
    have h1 : p * (xg : G) = (xg : G) * p := Subgroup.mem_centralizer_iff.mp hxgGc p hpP
    have h2 : p * (w * p) = p * (p * w) := by
      calc p * (w * p) = (p * w) * p := by group
        _ = (xg : G) * p := by rw [← hxw]
        _ = p * (xg : G) := h1.symm
        _ = p * (p * w) := by rw [hxw]
    exact mul_left_cancel h2
  have hw1 : w ≠ 1 := by
    intro h1
    exact hnotP (by rw [hxw, h1, mul_one]; exact hpP)
  have hwcent : ∀ q ∈ P, q⁻¹ * w * q = w := by
    intro q hq
    have hpq : p * q = q * p := hPab p hpP q hq
    have hxq : q * (xg : G) = (xg : G) * q := Subgroup.mem_centralizer_iff.mp hxgGc q hq
    have hpinv : p⁻¹ * q = q * p⁻¹ :=
      (Commute.inv_left (show Commute p q from hpq)).eq
    have hwq : w * q = q * w := by
      calc w * q = (p⁻¹ * (xg : G)) * q := by rw [hweq]
        _ = p⁻¹ * ((xg : G) * q) := by group
        _ = p⁻¹ * (q * (xg : G)) := by rw [hxq.symm]
        _ = (p⁻¹ * q) * (xg : G) := by group
        _ = (q * p⁻¹) * (xg : G) := by rw [hpinv]
        _ = q * (p⁻¹ * (xg : G)) := by group
        _ = q * w := by rw [hweq]
    calc q⁻¹ * w * q = q⁻¹ * (w * q) := by rw [mul_assoc]
      _ = q⁻¹ * (q * w) := by rw [hwq]
      _ = w := by group
  -- ## 14.  assembly
  refine ⟨(xg : G), hxV, hxgF, ?_, hnotP, w, hwW, hw1, hwcent, ?_⟩
  · intro q hq
    have h1 : q * (xg : G) = (xg : G) * q := Subgroup.mem_centralizer_iff.mp hxgGc q hq
    calc q⁻¹ * (xg : G) * q = q⁻¹ * ((xg : G) * q) := by rw [mul_assoc]
      _ = q⁻¹ * (q * (xg : G)) := by rw [h1.symm]
      _ = (xg : G) := by group
  · have hwpinv : w⁻¹ * p = p * w⁻¹ :=
      (Commute.inv_left (show Commute w p from hwp)).eq
    have hfin : w⁻¹ * (xg : G) = p := by
      rw [hxw]
      calc w⁻¹ * (p * w) = (w⁻¹ * p) * w := by group
        _ = (p * w⁻¹) * w := by rw [hwpinv]
        _ = p := by group
    rw [hfin]
    exact hpP

end Work.PSU3.StageB.NotFpfStep4
