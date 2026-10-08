/-
# Ch. III §4 Prop. 2 (b): the auxiliary cardinality/counting identities

This module records the counting content that the proof of §4 Prop. 2 (b) (and of Prop. 2 (c),(d))
uses.  With `D = twoPoint H t`, `E = Egrp H t W = W ⊓ D`, `E' = Ecomm H t W = ⁅E,E⁆`,
`V = centD H t = C_D(t)`, `C = A ⊓ C_G(P)`:

* `|E'| · p = |E|` and `p ∤ |E'|` (Lemma 1 (d): `E = E' ⋊ P` and `P` is a `p`-Sylow of `E`);
* `|D| = |E'| · p · |C|` (Prop. 1: `E` is a normal complement of `C` in `D`, and `E` is the group
  above);
* `|D:E'| = p·|C|` and `|D:C| = |E'|·p` (the index/cardinality identities for `E' ≤ D`, `C ≤ D`);
* `|K| · |A| = |E'| · |C|` (App. I (1)(a): `|K| = |D:V|`, and `V = A ⋊ P` gives `|V| = |A|·p`).

Nothing here uses nilpotency or Hall-ness: this is pure counting, which is why it is stated as a
separate lemma from `Prop2bConc`.
-/
import Mathlib
import Submission.Work.NormalComplement.NC4.Defs
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.sec4_P2d

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.NormalComplement.Design

namespace Work.NormalComplement.NC4

theorem prop2b_aux_counts {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (h1d : Work.NormalComplement.NC4.Lemma1dConc H t W p P A)
    (hP1 : Work.NormalComplement.NC4.Prop1Conc H t W p P A)
    (h2a : Work.NormalComplement.NC4.Prop2aConc H t W p P A) :
    Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) * p =
        Nat.card ↥(Work.NormalComplement.Design.Egrp H t W) ∧
      ¬ p ∣ Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) ∧
      Nat.card ↥(Submission.Blueprint.twoPoint H t) =
        Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) * p *
          Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) ∧
      (Work.NormalComplement.Design.Ecomm H t W).relIndex (Submission.Blueprint.twoPoint H t) =
        p * Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) ∧
      (A ⊓ Subgroup.centralizer (P : Set G)).relIndex (Submission.Blueprint.twoPoint H t) =
        Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) * p ∧
      (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t).ncard * Nat.card ↥A =
        Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) *
          Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
  have hp : p.Prime := h.prime
  have hp_pos : 0 < p := hp.pos
  let D : Subgroup G := twoPoint H t
  let E : Subgroup G := Egrp H t W
  let E' : Subgroup G := Ecomm H t W
  let V : Subgroup G := centD H t
  let C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G)
  have hE_sup : E' ⊔ P = E := h1d.2.2
  have hE_inf : E' ⊓ P = ⊥ := h1d.2.1
  have hP_le_E : P ≤ E := hE_sup ▸ le_sup_right
  have hE_le_D : E ≤ D := inf_le_right
  have hE'_le_E : E' ≤ E :=
    (Subgroup.commutator_le_sup E E).trans (le_of_eq (sup_idem E))
  have hE'_le_D : E' ≤ D := hE'_le_E.trans hE_le_D
  have hC_le_A : C ≤ A := inf_le_left
  have hC_le_V : C ≤ V := hC_le_A.trans h.A_le
  have hC_le_D : C ≤ D := hC_le_V.trans inf_le_left
  have hP_le_V : P ≤ V := h.P_le.trans inf_le_right
  have hV_le_D : V ≤ D := inf_le_left
  -- `E'` is normalised by `E` (hence by `P ≤ E`)
  have hE'_norm : E ≤ Subgroup.normalizer (E' : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer he)]
  have hP_norm_E' : P ≤ Subgroup.normalizer (E' : Set G) := hP_le_E.trans hE'_norm
  -- ## `|E'| * p = |E|` and `p ∤ |E'|`
  have hcardE : Nat.card ↥E' * p = Nat.card ↥E := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := E') (K := P) hP_norm_E'
    rw [hE_sup, hE_inf, Subgroup.card_bot, mul_one, h.P_card] at h1
    exact h1.symm
  have hP_sylE : Work.NormalComplement.IsSylowIn p P E :=
    Work.NormalComplement.sylowIn_of_le_of_le h1d.1 hP_le_E hE_le_D
  have hrelE : P.relIndex E = Nat.card ↥E' := by
    have h1 : P.relIndex E * Nat.card ↥P = Nat.card ↥E :=
      Work.NormalComplement.relIndex_mul_card_of_le' hP_le_E
    rw [h.P_card] at h1
    have h2 : P.relIndex E * p = Nat.card ↥E' * p := by rw [h1, ← hcardE]
    exact Nat.eq_of_mul_eq_mul_right hp_pos h2
  have hE'_ne : ¬ p ∣ Nat.card ↥E' := by
    rw [← hrelE]; exact hP_sylE.2.2
  -- ## Proposition 1: `E` is a normal complement of `C = A ⊓ C_G(P)` in `D`
  have hN_eq : (Work.NormalComplement.Kgrp (twoPoint H t) t ⊔ commSub A P) ⊔ P = E :=
    h2a.1.symm
  have hD_le_NG_E : D ≤ Subgroup.normalizer (E : Set G) := by
    have h1 := hP1.2.2.2.2.1
    rwa [hN_eq] at h1
  have hE_inf_C : E ⊓ C = ⊥ := by
    have h1 := hP1.2.2.2.2.2.1
    rwa [hN_eq] at h1
  have hE_sup_C : E ⊔ C = D := by
    have h1 := hP1.2.2.2.2.2.2
    rwa [hN_eq] at h1
  have hcardD : Nat.card ↥D = Nat.card ↥E * Nat.card ↥C := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := E) (K := C)
      (hC_le_D.trans hD_le_NG_E)
    rw [hE_sup_C, hE_inf_C, Subgroup.card_bot, mul_one] at h1
    exact h1
  -- ## `|D| = |E'| * p * |C|`
  have h3 : Nat.card ↥D = Nat.card ↥E' * p * Nat.card ↥C := by
    rw [hcardD, hcardE]
  have hE'_pos : 0 < Nat.card ↥E' := Nat.card_pos_iff.mpr ⟨⟨1, E'.one_mem⟩, inferInstance⟩
  have hC_pos : 0 < Nat.card ↥C := Nat.card_pos_iff.mpr ⟨⟨1, C.one_mem⟩, inferInstance⟩
  -- ## the two relative indices
  have h4 : E'.relIndex D = p * Nat.card ↥C := by
    have h1 : E'.relIndex D * Nat.card ↥E' = Nat.card ↥D :=
      Work.NormalComplement.relIndex_mul_card_of_le' hE'_le_D
    have h2 : E'.relIndex D * Nat.card ↥E' = p * Nat.card ↥C * Nat.card ↥E' := by
      rw [h1, h3]; ring
    exact Nat.eq_of_mul_eq_mul_right hE'_pos h2
  have h5 : C.relIndex D = Nat.card ↥E' * p := by
    have h1 : C.relIndex D * Nat.card ↥C = Nat.card ↥D :=
      Work.NormalComplement.relIndex_mul_card_of_le' hC_le_D
    have h2 : C.relIndex D * Nat.card ↥C = Nat.card ↥E' * p * Nat.card ↥C := by
      rw [h1, h3]
    exact Nat.eq_of_mul_eq_mul_right hC_pos h2
  -- ## `|K| * |A| = |E'| * |C|`
  have hcardV : Nat.card ↥V = Nat.card ↥A * p := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := A) (K := P)
      (hP_le_V.trans h.A_normal)
    rw [h.A_sup, h.A_inf, Subgroup.card_bot, mul_one, h.P_card] at h1
    exact h1
  have hD_odd : Odd (Nat.card ↥D) := h.se.2.2 t h.notMem
  have hcopD : Nat.Coprime (Nat.card ↥D) 2 := Nat.coprime_two_right.mpr hD_odd
  have hnormD : Work.NormalComplement.NormalizedBy t D :=
    Work.NormalComplement.normalizedBy_twoPoint h.invol
  -- App. I (1)(a): `|K| = |D : V|`
  have hKset_card : (Work.NormalComplement.Kset D t).ncard = V.relIndex D := by
    obtain ⟨hKappIdx, hDcomp⟩ :=
      Work.NormalComplement.appI_one (d := 2) Nat.prime_two h.invol hnormD hcopD
    obtain ⟨hKsetEq, -⟩ := hDcomp rfl
    have h1 : (Work.NormalComplement.Kset D t).ncard
        = ((Subgroup.centralizer ({t} : Set G) ⊓ D).subgroupOf D).index := by
      rw [← hKsetEq, hKappIdx]
    have hVD : Subgroup.centralizer ({t} : Set G) ⊓ D = V := by
      show Subgroup.centralizer ({t} : Set G) ⊓ D = centD H t
      rw [inf_comm]
    rw [h1, hVD, Subgroup.relIndex]
  have hcard6 : (Work.NormalComplement.Kset D t).ncard * Nat.card ↥A
      = Nat.card ↥E' * Nat.card ↥C := by
    have hkey : (Work.NormalComplement.Kset D t).ncard * Nat.card ↥A * p
        = V.relIndex D * Nat.card ↥V := by
      rw [hKset_card, hcardV]; ring
    have hVrel : V.relIndex D * Nat.card ↥V = Nat.card ↥D :=
      Work.NormalComplement.relIndex_mul_card_of_le' hV_le_D
    have hbig : (Work.NormalComplement.Kset D t).ncard * Nat.card ↥A * p
        = Nat.card ↥E' * Nat.card ↥C * p := by
      rw [hkey, hVrel, h3]; ring
    exact Nat.eq_of_mul_eq_mul_right hp_pos hbig
  exact ⟨hcardE, hE'_ne, h3, h4, h5, hcard6⟩

end Work.NormalComplement.NC4
