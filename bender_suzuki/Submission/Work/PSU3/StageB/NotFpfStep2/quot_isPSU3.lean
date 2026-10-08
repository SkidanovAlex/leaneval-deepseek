import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.NotFpfStep2.cW_ne_bot
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_P
import Submission.Work.PSU3.StageB.centralizer_oddResidual_isPSU3_v2
import Submission.Work.PSU3.StageB.card_centralizer_eq_cube_acyclic
import Submission.Work.PSU3.StageB.card_map_sylow_eq
import Submission.Work.PSU3.StageB.ncard_involutions_inf_H
import Submission.Work.PSU3.StageB.ncard_involutions_map_inf
import Submission.Work.PSU3.StageB.t_mem_and_center_quotient
import Submission.Work.PSU3.StageB.isSplitRankOne_map_of_surjective
import Submission.Work.PSU3.StageB.exists_PSU3_of_card_sylow_eq_cube
import Submission.Work.PSU3.StageB.Wiring
import Submission.Work.PSU3.StageA.lemma2cHig
import Submission.Work.PSU3.StageB.SemiregVendored
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.isSplitRankOneTransfer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep2

open LeanEval.GroupTheory.Defs

/-- The centre of a finite group lies in every strongly embedded subgroup: a central element
`z ∉ H` would give `H ⊓ H^z = H` of odd order, contradicting `H` even. -/
private theorem center_le_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) : Subgroup.center G ≤ H := by
  intro z hz
  by_contra hzH
  have hodd := hH.2.2 z hzH
  have hle : H ≤ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) H := by
    intro x hx
    refine ⟨z⁻¹ * x * z, ?_, ?_⟩
    · have hcomm : x * z = z * x := (Subgroup.mem_center_iff.mp hz) x
      have hzx : z⁻¹ * x * z = x := by
        rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hzx]; exact hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hconj : H ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) H = H :=
    inf_eq_left.mpr hle
  rw [hconj] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hH.2.1

/-- **Peterfalvi II Ch. VII §4 (1)**, in the `NotFpf` setting: with the extra case-(c) inputs
`|Q| = |Q₀|³` and `W ≠ ⊥` and the Galois input `Z(U) ≤ V`, the quotient `U/Z(U)` of
`U = O^{2'}(C_G(P))` by its centre is `PSU(3, 2ⁿ)` and `|C_{Q₀}(P)| = 2ⁿ`, `n ≥ 2`.

The proof assembles the reduction of `Submission/Work/PSU3/StageB/centralizer_oddResidual_isPSU3_v2`:
`caseC_data_of_W_ne_bot` gives `orderOf (s * t) = 3` from `W ≠ ⊥`, the local trichotomy
`card_centralizer_eq_cube_acyclic` gives `|C_Q(P)| = |C_{Q₀}(P)|³`, the P3 clause of
`ChIIFourProp` at `X = P` supplies the Sylow `S` and the epimorphism `φ : ↥U ↠ Y` onto a simple
Bender group `Y` with kernel `Z(U)`, `center_le_P` + `card_map_sylow_eq` give `|U_Y| = |C_Q(P)|`,
`ncard_involutions_inf_H` + `ncard_involutions_map_inf` give `#Inv(B_Y) + 1 = |C_{Q₀}(P)|`, the
datum `IsSplitRankOne B_Y U_Y w_Y` is transferred along `φ` by `isSplitRankOneTransfer`, and
`isPSU3_of_step4_data` closes the loop. -/
theorem quot_isPSU3 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hQ3 : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) (hW : Work.ThmF.W H t ≠ ⊥)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    (hPne : P ≠ ⊥) {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y)
    (hZV : (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
      (Work.PSU3.StageB.centralizerOddResidual P).subtype ≤ Submission.Blueprint.centD H t) :
    ∃ n' : ℕ, 2 ≤ n' ∧
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) = 2 ^ n' ∧
      Nonempty (↥(Work.PSU3.StageB.centralizerOddResidual P) ⧸
        (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)) ≃*
          LeanEval.GroupTheory.Defs.PSU3Model n') := by
  classical
  let F : Subgroup G := Work.PSU3.StageB.centralizerOddResidual P
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hS.split
  have hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H := hsplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  -- ## 0. the ambient structure identity `orderOf (s * t) = 3`
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  obtain ⟨-, hst3, -⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hW
  -- ## 1. Ch. II §4 Prop. 3 at `X = P`
  have hP1b := (hC4 G hS.situation H hH t ht2 htH).1
  have hP3 := (hC4 G hS.situation H hH t ht2 htH).2.2.2.1
  have hP4 : Submission.Blueprint.HasFourGroup ↥(Subgroup.centralizer (P : Set G)) :=
    hS.B3 P hPV hPp
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht2 htH hPV
  obtain ⟨k0, hk0K, hk01, hk0N⟩ :=
    Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hPV hX3 hP4 hP1b
  have hP3c := hP3 P hPne hPV ⟨k0, hk0K, hk01, hk0N⟩
  dsimp only at hP3c
  obtain ⟨-, ⟨S, hSp, hSFH, hSidx, hSNorm, hSD, hSsup⟩, ⟨hZc, hYZc⟩, -⟩ := hP3c
  obtain ⟨Y, hYG, φ, hφsurj, hφker, hYbender⟩ := hYZc
  letI : Group Y := hYG
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  -- restate the P3 fields with `F`
  have hSFH' : S ≤ F ⊓ H := hSFH
  have hSidx' : ¬ 2 ∣ (S.subgroupOf (F ⊓ H)).index := hSidx
  have hZc' : Submission.Blueprint.oddCore ↥F = Subgroup.center ↥F := hZc
  have hφker' : φ.ker = Subgroup.center ↥F := hφker
  -- ## 2. `t ∈ F`, hence `F` is `t`-invariant
  have htF : t ∈ F := (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).1
  have hFle : F ≤ Subgroup.centralizer (P : Set G) := by
    change Work.PSU3.StageB.centralizerOddResidual P ≤ Subgroup.centralizer (P : Set G)
    simp only [Work.PSU3.StageB.centralizerOddResidual]
    exact Subgroup.map_subtype_le _
  -- ## 3. `(H ⊓ F).subgroupOf F` is strongly embedded in `↥F`
  have hHF : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((H ⊓ F).subgroupOf F) := by
    have hInv : Submission.Blueprint.involutions
        (Subgroup.centralizer (P : Set G) : Set G) ⊆ F := by
      intro x hx
      change x ∈ Work.PSU3.StageB.centralizerOddResidual P
      exact Work.PSU3.StageA.mem_map_oddResidual_of_orderOf_eq_two_pow
        (C := Subgroup.centralizer (P : Set G)) hx.1 (k := 1) (by rw [hx.2, pow_one])
    have hFN : F ≤ Subgroup.normalizer (P : Set G) :=
      hFle.trans (Subgroup.centralizer_le_normalizer (P : Set G))
    have hPH : P ≤ Submission.Blueprint.conj (1 : G) H := by
      rw [Work.DoubleTransitivity.conj_one]
      exact fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hPV hx)).1).1
    have hres := hP1b P F hX3 hInv hFN 1 hPH
    rwa [Work.DoubleTransitivity.conj_one, inf_comm] at hres
  -- ## 4. the split rank-one datum in `Y = F/Z(F)`
  have hkerH : φ.ker ≤ (H ⊓ F).subgroupOf F := by
    rw [hφker']
    exact center_le_of_isStronglyEmbedded hHF
  have hoddKer : Odd (Nat.card φ.ker) := by
    rw [hφker', ← hZc']
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have himgSemb : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      (((H ⊓ F).subgroupOf F).map φ) :=
    Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd φ hφsurj hoddKer hkerH hHF
  obtain ⟨Pmd, hPmdB⟩ := Work.PSU3.StageA.modelDataBorel hYbender himgSemb
  have hmod : ∃ (P : Work.Models.ModelData Y), P.B = ((H ⊓ F).subgroupOf F).map φ :=
    ⟨Pmd, hPmdB⟩
  have htF' : (⟨t, htF⟩ : ↥F) ∉ (H ⊓ F).subgroupOf F := by
    intro hmem
    exact htH (Subgroup.mem_subgroupOf.mp hmem).1
  have htF2 : orderOf (⟨t, htF⟩ : ↥F) = 2 := by
    rw [Subgroup.orderOf_mk]; exact ht2
  have hSF_le : S.subgroupOf F ≤ (H ⊓ F).subgroupOf F := by
    intro x hx
    have hxS : (x : G) ∈ S := hx
    exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_inf.mp (hSFH' hxS)).2, x.2⟩
  have hSF : S ≤ F := hSFH'.trans inf_le_left
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
    refine le_antisymm (sup_le (le_inf (hSFH'.trans inf_le_right) (hSFH'.trans inf_le_left))
      (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)) ?_
    intro x hx
    obtain ⟨hxH, hxF⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.centralizer_le_normalizer (P : Set G) (hFle hxF)
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
      (le_inf inf_le_left (inf_le_right.trans (hFle.trans
        (Subgroup.centralizer_le_normalizer (P : Set G))))).trans hSNorm
    rw [Commons.GroupTheory.Subgroup.normalizer_subgroupOf S F hSF]
    exact Subgroup.subgroupOf_mono F (le_inf hHFN inf_le_right)
  have hSp' : IsPGroup 2 ↥(S.subgroupOf F) := by
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    exact IsPGroup.of_card (n := k)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hSFH'.trans inf_le_left)).toEquiv, hk])
  have hdatum : Submission.Blueprint.IsSplitRankOne
      (((H ⊓ F).subgroupOf F).map φ) (((S.subgroupOf F).map φ)) (φ ⟨t, htF⟩) :=
    Work.PSU3.StageA.isSplitRankOneTransfer hHF htF2 htF' hZc' hφsurj hφker' hmod
      hSp' hSF_le hSPnorm hSF_inf hSF_sup
  -- ## 5. the cardinality data
  have hZPsub : Subgroup.center ↥F ≤ P.subgroupOf F :=
    center_le_P hS hC4 hHig hQ3 hW hPV hPp hyQ hy0 hyc hZV
  have hZP : (Subgroup.center ↥F).map F.subtype ≤ P := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_subgroupOf.mp (hZPsub hu)
  have hS_le_H : S ≤ H := fun x hx => (Subgroup.mem_inf.mp (hSFH' hx)).2
  have hQHindex : (Q.subgroupOf H).index = Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    have hcard := Subgroup.card_mul_index (Q.subgroupOf H)
    have h1 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsplit.le).toEquiv
    rw [h1, Work.ThmF.split_card_H hsplit] at hcard
    exact Nat.mul_left_cancel Nat.card_pos hcard
  have hS_le_Q : S ≤ Q := by
    intro x hx
    haveI : (Q.subgroupOf H).Normal := Work.ThmF.split_Q_normal_in_H hsplit
    obtain ⟨n, hn⟩ := hSp (⟨x, hx⟩ : ↥S)
    have hxn : (⟨x, hS_le_H hx⟩ : ↥H) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg (fun g : ↥S => (g : G)) hn
      simpa using this
    exact Work.PSU3.StageA.mem_of_pow_two_eq_one_of_normal_odd_index (N := Q.subgroupOf H)
      (by rw [hQHindex]; exact hDodd) hxn
  have hZS : S ⊓ (Subgroup.center ↥F).map F.subtype = ⊥ :=
    Work.PSU3.StageB.inf_center_centralizerOddResidual_eq_bot hS hPV hZP hS_le_Q
  have hcardC : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G))
      = (Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))) ^ 3 :=
    Work.PSU3.StageB.card_centralizer_eq_cube_acyclic hS hC4 Work.PSU3.benderSTProp
      hs hs2 hr hsr hst3 hPV hPp hyQ hy0 hyc
  have hinv_raw : (Submission.Blueprint.involutions ((F ⊓ H : Subgroup G) : Set G)).ncard + 1
      = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) :=
    Work.PSU3.StageB.ncard_involutions_inf_H hS hC4 hPV
  have hinvmap : (Submission.Blueprint.involutions
        ((((H ⊓ F).subgroupOf F).map φ : Subgroup Y) : Set Y)).ncard
      = (Submission.Blueprint.involutions ((F ⊓ H : Subgroup G) : Set G)).ncard :=
    Work.PSU3.StageB.ncard_involutions_map_inf hS hPV hZP hφker'
  have hinv : (Submission.Blueprint.involutions
        ((((H ⊓ F).subgroupOf F).map φ : Subgroup Y) : Set Y)).ncard + 1
      = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := by
    rw [hinvmap]; exact hinv_raw
  have hcardU : Nat.card ↥(((S.subgroupOf F).map φ : Subgroup Y))
      = Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) :=
    Work.PSU3.StageB.card_map_sylow_eq hS hPV hPp hSp hSFH' hSidx' hφker' hZS
  obtain ⟨eY⟩ := (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).2 φ hφsurj hφker'
  -- ## 6. close
  obtain ⟨n', hn'2, hn'card, hiso⟩ :=
    Work.PSU3.StageB.isPSU3_of_step4_data hYbender hdatum rfl hinv hcardC hcardU eY
  exact ⟨n', hn'2, hn'card, hiso⟩

end Work.PSU3.StageB.NotFpfStep2
