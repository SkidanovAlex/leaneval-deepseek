import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec3_prop1
import Submission.Work.NormalComplement.sec2_lemma1
import Submission.Work.NormalComplement.sec1_lemma3_structure
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.sec4_P2d

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **Ch. III §3 Corollary of Proposition 2, first case** (p.178): if `E' ⊓ V = 1` then the
`FrobPacket` holds, directly from `sec2_lemma1`: `K ⊆ E'` and `E' ⊓ V = 1` give `⟨K⟩ ⊓ V = 1`
(by App. I (4), `|⟨K⟩| = |K|·|V ⊓ ⟨K⟩|`), so `⟨K⟩ = K` and every element of `(E ⊓ V)#` lies outside
`E'`, hence acts fixed-point-freely on `K`.  Also needs App. I (4) (`appI_four`: `D ≤ N(⟨Kset⟩)`,
`D = ⟨Kset⟩ ⊔ V`) and App. I (1) (`appI_one`: the counting giving `⟨Kset⟩ = Kset`). -/
theorem sec3_cor_case1 (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type} [Group G]
    [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    (h : Work.NormalComplement.Design.Setup3 G H t W)
    (hE'V : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t = ⊥) :
    Work.NormalComplement.Design.FrobPacket H t W := by
  -- ## The standing facts of the situation
  have ht : orderOf t = 2 := h.invol
  have htD : NormalizedBy t (twoPoint H t) := normalizedBy_twoPoint (H := H) ht
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have hcop : Nat.Coprime (Nat.card ↥(twoPoint H t)) 2 := Nat.coprime_two_right.mpr hDodd
  -- ## App. I (1) and (4), and §2 Lemma 1
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two ht htD hcop).2 rfl).1
  have hfour := appI_four (d := 2) Nat.prime_two ht htD hcop
  have h2 := sec2_lemma1 hFT h
  -- ## The candidate kernel `Kg = ⟨Kset D t⟩`
  set Kg : Subgroup G := Kgrp (twoPoint H t) t with hKgdef
  have hKg_closure : Kg = Subgroup.closure (Kapp t (twoPoint H t)) := by
    rw [hKgdef, Kgrp, ← hKappKset]
  have hcen_comm : Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t = centD H t := by
    rw [centD, inf_comm]
  have hV_le_D : centD H t ≤ twoPoint H t := inf_le_left
  -- ### `D = ⟨K⟩ · V` (App. I (4))
  have hD_eq : twoPoint H t = Kg ⊔ centD H t := by
    rw [hKg_closure, ← hcen_comm]
    exact hfour.2.2.2.1.symm
  -- ### `D` normalises `⟨K⟩` (App. I (4))
  have hK_norm : twoPoint H t ≤ Subgroup.normalizer ((Kg : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hxD k hk
    have hk' : k ∈ Subgroup.closure (Kapp t (twoPoint H t)) := by
      rw [← hKg_closure]; exact hk
    have hh := hfour.2.2.1 x hxD k hk'
    rw [hKg_closure]
    exact hh
  -- ### `K ⊆ E'` (§2 Lemma 1), hence `⟨K⟩ ≤ E' ≤ E ≤ W`
  have hKg_le_Ecomm : Kg ≤ Design.Ecomm H t W := by
    rw [hKgdef, Kgrp]
    exact (Subgroup.closure_le (Design.Ecomm H t W)).mpr h2.1
  have hKg_le_D : Kg ≤ twoPoint H t := by
    rw [hKg_closure]
    exact (Subgroup.closure_le (twoPoint H t)).mpr hfour.1
  have hEcomm_le_Egrp : Design.Ecomm H t W ≤ Design.Egrp H t W := by
    show ⁅Design.Egrp H t W, Design.Egrp H t W⁆ ≤ Design.Egrp H t W
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (Design.Egrp H t W).mul_mem
      ((Design.Egrp H t W).mul_mem
        ((Design.Egrp H t W).mul_mem ha hb) ((Design.Egrp H t W).inv_mem ha))
      ((Design.Egrp H t W).inv_mem hb)
  have hKg_le_W : Kg ≤ W := hKg_le_Ecomm.trans (hEcomm_le_Egrp.trans inf_le_left)
  -- ### `V ⊓ ⟨K⟩ = 1` (from `E' ⊓ V = 1`)
  have hVK : centD H t ⊓ Kg = ⊥ := by
    have hle : centD H t ⊓ Kg ≤ Design.Ecomm H t W ⊓ centD H t :=
      le_inf (fun x hx => hKg_le_Ecomm hx.2) inf_le_left
    rw [hE'V] at hle
    exact le_bot_iff.mp hle
  -- ### `|⟨K⟩| = |K|` (App. I (4))
  have hcard : Nat.card ↥Kg = (Kset (twoPoint H t) t).ncard := by
    have h7 := hfour.2.2.2.2.2.2
    rw [← hKg_closure] at h7
    rw [hcen_comm, hVK, Subgroup.card_bot, mul_one, hKappKset] at h7
    exact h7
  -- ### `⟨K⟩ = K` as sets
  have hKg_eq_Kset : (Kg : Set G) = Kset (twoPoint H t) t := by
    have hsub : Kset (twoPoint H t) t ⊆ (Kg : Set G) := by
      rw [hKg_closure, hKappKset]
      exact Subgroup.subset_closure
    have hle : (Kg : Set G).ncard ≤ (Kset (twoPoint H t) t).ncard := by
      rw [← Nat.card_coe_set_eq (Kg : Set G)]
      exact le_of_eq hcard
    exact (Set.eq_of_subset_of_ncard_le hsub hle).symm
  -- ## Assemble the `FrobPacket`
  refine ⟨Kg, hKg_eq_Kset, ?_, ?_, ?_, ?_⟩
  · -- `E` normalises `K`
    intro w hw k hk
    exact (Subgroup.le_normalizer_iff.mp hK_norm) w hw.2 k hk
  · -- `K ⊓ (W ⊓ V) = 1`
    have hle : Kg ⊓ (W ⊓ centD H t) ≤ centD H t ⊓ Kg :=
      le_inf (fun x hx => hx.2.2) (fun x hx => hx.1)
    rw [hVK] at hle
    exact le_bot_iff.mp hle
  · -- `K ⊔ (W ⊓ V) = W ⊓ D`
    refine le_antisymm ?_ ?_
    · exact sup_le (le_inf hKg_le_W hKg_le_D)
        (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    · intro e he
      obtain ⟨heW, heD⟩ := Subgroup.mem_inf.mp he
      have he_sup : e ∈ Kg ⊔ centD H t := by rw [← hD_eq]; exact heD
      have hcoprod : (↑(Kg ⊔ centD H t) : Set G) = (Kg : Set G) * (centD H t : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left Kg (centD H t)
          (inf_le_left.trans hK_norm)
      change e ∈ (↑(Kg ⊔ centD H t) : Set G) at he_sup
      rw [hcoprod] at he_sup
      obtain ⟨k, hkKg, v, hvV, hkv⟩ := Set.mem_mul.mp he_sup
      have hvW : v ∈ W := by
        have hv_eq : v = k⁻¹ * e := by rw [← hkv]; group
        rw [hv_eq]
        exact W.mul_mem (W.inv_mem (hKg_le_W hkKg)) heW
      rw [← hkv]
      exact Subgroup.mul_mem_sup hkKg (Subgroup.mem_inf.mpr ⟨hvW, hvV⟩)
  · -- `(W ⊓ V)#` acts fixed-point-freely on `K` (§2 Lemma 1)
    intro k hk hk1 v hv hv1 hfix
    have hkKset : k ∈ Kset (twoPoint H t) t := by
      rw [← hKg_eq_Kset]; exact hk
    have hvEgrp : v ∈ Design.Egrp H t W ⊓ centD H t :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hv.1, hV_le_D hv.2⟩, hv.2⟩
    have hv_notE : v ∉ Design.Ecomm H t W := by
      intro hvE
      have hmem : v ∈ Design.Ecomm H t W ⊓ centD H t := ⟨hvE, hv.2⟩
      rw [hE'V] at hmem
      exact hv1 (Subgroup.mem_bot.mp hmem)
    exact hk1 (h2.2.2 v hvEgrp hv_notE k hkKset hfix)

end Work.NormalComplement
