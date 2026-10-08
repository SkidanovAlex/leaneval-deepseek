/-
Copied from `Submission/Work/A7F/pCore_two_centralizer.lean` with the import list adapted to the
CORE4 world (see the note below); the `Work.A7F` content is unchanged.

**Why a copy:**  the areas of this workspace each carry their own verbatim copy of the `Work.GW2`
vocabulary (`Contracts2.lean`), and two of them cannot be imported into one environment
(`environment already contains 'Work.GW2.A7ModelProp'`).  This file therefore takes the
`Work.GW2` vocabulary from `Submission.Work.CORE4.Defs` and imports `Submission.Work.A7.Defs`
(clash-free) instead of `Submission.Work.A7F.Defs`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.A7.Defs
import Submission.Work.CORE4.A7M.Defs
import Submission.Work.CORE4.A7M.Four
import Submission.Work.CORE4.A7M.PCoreDefs
import Submission.Work.CORE4.A7M.PCoreFacts
import Submission.Work.CORE4.A7M.CardCent

open scoped MatrixGroups

namespace Work.A7F

open Subgroup

theorem pCore_two_centralizer :
    Work.GW2.pCoreIn 2 (Subgroup.centralizer ({a7Invol} : Set (alternatingGroup (Fin 7)))) =
      a7V1 := by
  set C : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.centralizer ({a7Invol} : Set (alternatingGroup (Fin 7))) with hCdef
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCcard : Nat.card ↥C = 24 := card_centralizer_a7Invol
  -- basic inclusions
  have hSle : a7S ≤ C := by rw [hCdef]; exact a7S_le_centralizer
  have hS2le : a7S2 ≤ C := by rw [hCdef]; exact a7S2_le_centralizer
  have hV1S : a7V1 ≤ a7S := a7V1_le_a7S
  have hV1S2 : a7V1 ≤ a7S2 := a7V1_le_a7S2
  have hV1C : a7V1 ≤ C := hV1S.trans hSle
  have hsupC : a7S ⊔ Subgroup.zpowers Work.A7.a7ThreeCycle = C := by
    rw [hCdef]; exact a7S_sup_threeCycle
  -- `V₁` is normalized by `C`
  have hCleN : C ≤ Subgroup.normalizer (a7V1 : Set (alternatingGroup (Fin 7))) := by
    rw [← hsupC]
    exact sup_le a7S_le_normalizer a7zpowers_le_normalizer
  -- `M = V₁` pulled back to `C` is a normal `2`-subgroup of `C`
  have hMnorm : (a7V1.comap C.subtype).Normal := by
    refine ⟨fun m hm x => ?_⟩
    rw [Subgroup.mem_comap] at hm ⊢
    have hx : C.subtype x ∈ Subgroup.normalizer (a7V1 : Set (alternatingGroup (Fin 7))) :=
      hCleN x.2
    rw [Subgroup.mem_normalizer_iff] at hx
    simpa [map_mul, map_inv] using (hx (C.subtype m)).mp hm
  haveI : (a7V1.comap C.subtype).Normal := hMnorm
  have hMcard : Nat.card ↥(a7V1.comap C.subtype) = 4 := by
    have h1 : Nat.card ↥(Subgroup.map C.subtype (a7V1.comap C.subtype)) =
        Nat.card ↥(a7V1.comap C.subtype) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective C)
    rw [h1.symm, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.mpr hV1C,
      card_a7V1]
  have hMpg : IsPGroup 2 ↥(a7V1.comap C.subtype) :=
    IsPGroup.of_card (n := 2) (by rw [hMcard]; norm_num)
  -- the two explicit Sylow `2`-subgroups of `C`
  have hcardS : Nat.card ↥(a7S.comap C.subtype) = 8 := by
    have h1 : Nat.card ↥(Subgroup.map C.subtype (a7S.comap C.subtype)) =
        Nat.card ↥(a7S.comap C.subtype) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective C)
    rw [h1.symm, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.mpr hSle,
      card_a7S]
  have hcardS2 : Nat.card ↥(a7S2.comap C.subtype) = 8 := by
    have h1 : Nat.card ↥(Subgroup.map C.subtype (a7S2.comap C.subtype)) =
        Nat.card ↥(a7S2.comap C.subtype) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective C)
    rw [h1.symm, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.mpr hS2le,
      card_a7S2]
  have hpgS : IsPGroup 2 ↥(a7S.comap C.subtype) :=
    IsPGroup.of_card (n := 3) (by rw [hcardS]; norm_num)
  have hpgS2 : IsPGroup 2 ↥(a7S2.comap C.subtype) :=
    IsPGroup.of_card (n := 3) (by rw [hcardS2]; norm_num)
  have hndvdS : ¬ 2 ∣ (a7S.comap C.subtype).index := by
    intro hd
    have hmul := Subgroup.card_mul_index (a7S.comap C.subtype)
    rw [hcardS, hCcard] at hmul
    obtain ⟨m, hm⟩ := hd
    rw [hm] at hmul
    omega
  have hndvdS2 : ¬ 2 ∣ (a7S2.comap C.subtype).index := by
    intro hd
    have hmul := Subgroup.card_mul_index (a7S2.comap C.subtype)
    rw [hcardS2, hCcard] at hmul
    obtain ⟨m, hm⟩ := hd
    rw [hm] at hmul
    omega
  let P1 : Sylow 2 ↥C := hpgS.toSylow hndvdS
  let P2 : Sylow 2 ↥C := hpgS2.toSylow hndvdS2
  have hP1coe : (P1 : Subgroup ↥C) = a7S.comap C.subtype := by
    simp only [P1, IsPGroup.toSylow_coe]
  have hP2coe : (P2 : Subgroup ↥C) = a7S2.comap C.subtype := by
    simp only [P2, IsPGroup.toSylow_coe]
  -- `O_2(C)` is a normal `2`-subgroup, hence lies in both Sylow subgroups
  have hpcore : IsPGroup 2 ↥(Work.GW2.pCore 2 ↥C) := by
    have hsup : IsPGroup 2 ↥(sSup {N : Subgroup ↥C | N.Normal ∧ IsPGroup 2 N}) :=
      Sylow.sSup_of_normal _ (fun N hN => hN.2) (fun N hN => hN.1)
    exact hsup.to_le (Subgroup.normalCore_le _)
  haveI : (Work.GW2.pCore 2 ↥C).Normal := Work.GW2.pCore_normal 2 ↥C
  have hleP1 : Work.GW2.pCore 2 ↥C ≤ (P1 : Subgroup ↥C) :=
    IsPGroup.le_sylow_of_normal hpcore P1
  have hleP2 : Work.GW2.pCore 2 ↥C ≤ (P2 : Subgroup ↥C) :=
    IsPGroup.le_sylow_of_normal hpcore P2
  -- `M` lies in both Sylow subgroups, so in their intersection
  have hMleP1 : a7V1.comap C.subtype ≤ (P1 : Subgroup ↥C) := by
    rw [hP1coe]; exact Subgroup.comap_mono hV1S
  have hMleP2 : a7V1.comap C.subtype ≤ (P2 : Subgroup ↥C) := by
    rw [hP2coe]; exact Subgroup.comap_mono hV1S2
  have hMleInf : a7V1.comap C.subtype ≤ (P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C) :=
    le_inf hMleP1 hMleP2
  -- the two Sylow subgroups are distinct
  have hP1neP2 : (P1 : Subgroup ↥C) ≠ (P2 : Subgroup ↥C) := by
    intro h
    have hyC : a7y ∈ C := hSle a7y_mem_a7S
    have h1 : (⟨a7y, hyC⟩ : ↥C) ∈ (P1 : Subgroup ↥C) := by
      rw [hP1coe]; exact Subgroup.mem_subgroupOf.mpr a7y_mem_a7S
    have h2 : (⟨a7y, hyC⟩ : ↥C) ∈ (P2 : Subgroup ↥C) := h ▸ h1
    rw [hP2coe] at h2
    exact a7y_notMem_a7S2 h2
  have hcardP1 : Nat.card ↥(P1 : Subgroup ↥C) = 8 := by rw [hP1coe, hcardS]
  have hcardP2 : Nat.card ↥(P2 : Subgroup ↥C) = 8 := by rw [hP2coe, hcardS2]
  -- cardinality of the intersection
  have hdvdin : Nat.card ↥((P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C)) ∣ 8 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_left : (P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C) ≤ (P1 : Subgroup ↥C))
    rwa [hcardP1] at this
  have hneq : ((P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C)) ≠ (P1 : Subgroup ↥C) := by
    intro h
    have hle : (P1 : Subgroup ↥C) ≤ (P2 : Subgroup ↥C) := h ▸ inf_le_right
    have heq : (P1 : Subgroup ↥C) = (P2 : Subgroup ↥C) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP1, hcardP2])
    exact hP1neP2 heq
  have hlt : Nat.card ↥((P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C)) < 8 := by
    have hge : ¬ (8 ≤ Nat.card ↥((P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C))) := by
      intro hge'
      have heq : (P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C) = (P1 : Subgroup ↥C) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardP1]; exact hge')
      exact hneq heq
    omega
  have hle4 : Nat.card ↥((P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C)) ≤ 4 := by
    have hb := Nat.le_of_dvd (by norm_num : 0 < 8) hdvdin
    interval_cases Nat.card ↥((P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C)) <;> omega
  have hinf_eq_M : (P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C) = a7V1.comap C.subtype :=
    (Subgroup.eq_of_le_of_card_ge hMleInf (by rw [hMcard]; exact hle4)).symm
  -- conclusion
  have hpCore_eq : Work.GW2.pCore 2 ↥C = a7V1.comap C.subtype := by
    refine le_antisymm ?_ ?_
    · have h1 : Work.GW2.pCore 2 ↥C ≤ (P1 : Subgroup ↥C) ⊓ (P2 : Subgroup ↥C) :=
        le_inf hleP1 hleP2
      rwa [hinf_eq_M] at h1
    · have hMsSup : a7V1.comap C.subtype ≤
          sSup {N : Subgroup ↥C | N.Normal ∧ IsPGroup 2 N} :=
        le_sSup ⟨hMnorm, hMpg⟩
      have h1 : (a7V1.comap C.subtype).normalCore ≤
          (sSup {N : Subgroup ↥C | N.Normal ∧ IsPGroup 2 N}).normalCore :=
        Subgroup.normalCore_mono hMsSup
      rw [Subgroup.normalCore_eq_self] at h1
      exact h1
  rw [Work.GW2.pCoreIn, hpCore_eq, Subgroup.map_comap_eq, Subgroup.range_subtype,
    inf_eq_right.mpr hV1C]

end Work.A7F
