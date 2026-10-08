import Mathlib
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.ca_coprime
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.appI_five_b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.S5K
open Work.NormalComplement

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
  {p : ℕ} {P A : Subgroup G}

/-- Bundled prelude facts for `D = twoPoint H t`, `V = centD H t`, `Kg = Kgrp D t`. -/
lemma prop1_prep (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A) :
    (t * t = 1) ∧ NormalizedBy t (twoPoint H t) ∧ Odd (Nat.card ↥(twoPoint H t)) ∧
    Nat.Coprime (Nat.card ↥(twoPoint H t)) 2 ∧ Group.IsSolvable ↥(twoPoint H t) ∧
    (Kgrp (twoPoint H t) t = Work.NormalComplement.closureKapp t (twoPoint H t)) ∧
    (Kapp t (twoPoint H t) = Kset (twoPoint H t) t) ∧
    (twoPoint H t = Kgrp (twoPoint H t) t ⊔ centD H t) ∧
    (Nat.card ↥(Kgrp (twoPoint H t) t)
      = (Kset (twoPoint H t) t).ncard * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t)) ∧
    (Kgrp (twoPoint H t) t ≤ twoPoint H t) ∧
    (twoPoint H t ≤ Subgroup.normalizer ((Kgrp (twoPoint H t) t : Subgroup G) : Set G)) := by
  have ht2 : t * t = 1 := Work.NormalComplement.twoPoint_mul_self h.invol
  have htD : NormalizedBy t (twoPoint H t) := Work.NormalComplement.twoPoint_normalizedBy ht2
  have hodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have hcop : (Nat.card ↥(twoPoint H t)).Coprime 2 := Nat.coprime_two_right.mpr hodd
  have hsolv : Group.IsSolvable ↥(twoPoint H t) := hFT ↥(twoPoint H t) hodd
  have hfour := appI_four (d := 2) Nat.prime_two h.invol htD hcop
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two h.invol htD hcop).2 rfl).1
  have hcen : Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t = centD H t := by
    rw [centD, inf_comm]
  have hKg : Kgrp (twoPoint H t) t = Work.NormalComplement.closureKapp t (twoPoint H t) := by
    rw [Kgrp, ← hKappKset]
  have hD_eq : twoPoint H t = Kgrp (twoPoint H t) t ⊔ centD H t := by
    rw [hKg, ← hcen]; exact hfour.2.2.2.1.symm
  have hcardKg : Nat.card ↥(Kgrp (twoPoint H t) t)
      = (Kset (twoPoint H t) t).ncard * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t) := by
    have hinf : Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t ⊓
        Work.NormalComplement.closureKapp t (twoPoint H t)
        = Kgrp (twoPoint H t) t ⊓ centD H t := by
      rw [hKg, hcen]
      simp only [inf_assoc, inf_comm, inf_left_comm]
    conv_lhs => rw [hKg, hfour.2.2.2.2.2.2]
    rw [hinf, hKg, ← hKappKset]
  have hKg_le_D : Kgrp (twoPoint H t) t ≤ twoPoint H t := by
    rw [hKg]; exact (Subgroup.closure_le _).mpr hfour.1
  have hD_le_normKg : twoPoint H t ≤
      Subgroup.normalizer ((Kgrp (twoPoint H t) t : Subgroup G) : Set G) := by
    rw [hKg]
    exact Subgroup.le_normalizer_iff.mpr (fun x hx k hk => hfour.2.2.1 x hx k hk)
  exact ⟨ht2, htD, hodd, hcop, hsolv, hKg, hKappKset, hD_eq, hcardKg, hKg_le_D, hD_le_normKg⟩

/-- `P` is nontrivial. -/
lemma prop1_P_ne_bot (h : Design.Setup45A G H t W p P A) : P ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [h.P_card] at h1
  exact h.prime.ne_one h1

/-- `¬ p ∣ |⟨Kset D t⟩|`. -/
lemma prop1_notDvdKg (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : Design.Setup45A G H t W p P A) :
    ¬ p ∣ Nat.card ↥(Kgrp (twoPoint H t) t) := by
  obtain ⟨ht2, htD, -, hcop, hsolv, hKg, hKappKset, -, -, -, -⟩ := prop1_prep hFT h
  have hP_le_V : P ≤ centD H t := le_trans h.P_le inf_le_right
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hPp : IsPGroup p ↥P := by
    rw [IsPGroup.iff_card]; exact ⟨1, by rw [pow_one]; exact h.P_card⟩
  have hcen_comm : Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t = centD H t := by
    rw [centD, inf_comm]
  have hP_fixX : P ≤ fixX t (twoPoint H t) := by
    have : P ≤ Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t := by
      rw [hcen_comm]; exact hP_le_V
    exact this
  have hfpfKapp : ∀ k ∈ Kapp t (twoPoint H t), (∀ u ∈ P, u * k * u⁻¹ = k) → k = 1 :=
    kapp_fixed_eq_one_of_fpf (prop1_P_ne_bot h) (fun u hu hu1 k hk hfix => by
      refine h.P_fpf u hu hu1 k ?_ hfix
      rwa [hKappKset] at hk)
  rw [hKg]
  exact not_dvd_card_closureKapp h.prime Nat.prime_two h.invol htD hcop hsolv hP_fixX hPp hfpfKapp

/-- `p ∤ |A|`. -/
lemma prop1_notDvdCardA (h : Design.Setup45A G H t W p P A)
    (hPsyl : IsSylowIn p P (twoPoint H t)) : ¬ p ∣ Nat.card ↥A := by
  intro hpA
  have hcardV : Nat.card ↥(centD H t) = Nat.card ↥A * p := by
    have hh := card_sup_mul_card_inf (H := A) (K := P)
      (le_trans h.P_le (le_trans inf_le_right h.A_normal))
    rw [h.A_sup, h.A_inf, Subgroup.card_bot, h.P_card, mul_one] at hh
    exact hh
  have hcardD : Nat.card ↥(twoPoint H t) = p * (P.subgroupOf (twoPoint H t)).index := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf (twoPoint H t))
    have h2 : Nat.card ↥(P.subgroupOf (twoPoint H t)) = p := by
      rw [← h.P_card]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPsyl.2.1).toEquiv
    rw [h2] at h1; exact h1.symm
  have hdvdV : p * p ∣ Nat.card ↥(centD H t) := by
    rw [hcardV]; exact Nat.mul_dvd_mul hpA (dvd_refl p)
  have hdvdD : p * p ∣ Nat.card ↥(twoPoint H t) :=
    dvd_trans hdvdV (Subgroup.card_dvd_of_le inf_le_left)
  rw [hcardD] at hdvdD
  exact hPsyl.2.2 (Nat.dvd_of_mul_dvd_mul_left h.prime.pos hdvdD)

/-- `⟨Kset D t⟩ ⊓ V ≤ A`. -/
lemma prop1_NleA (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : Design.Setup45A G H t W p P A)
    (hPsyl : IsSylowIn p P (twoPoint H t)) :
    Kgrp (twoPoint H t) t ⊓ centD H t ≤ A := by
  obtain ⟨ht2, htD, hodd, hcop, hsolv, hKg, hKappKset, hD_eq, hcardKg, hKg_le_D, hD_le_normKg⟩ :=
    prop1_prep hFT h
  set N : Subgroup G := Kgrp (twoPoint H t) t ⊓ centD H t with hNdef
  have hNleV : N ≤ centD H t := inf_le_right
  have hNnormV : centD H t ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv x hx
    obtain ⟨hxK, hxV⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hD_le_normKg hv.1) x).mp hxK
    · exact (centD H t).mul_mem ((centD H t).mul_mem hv hxV) ((centD H t).inv_mem hv)
  have hcardV : Nat.card ↥(centD H t) = Nat.card ↥A * p := by
    have hh := card_sup_mul_card_inf (H := A) (K := P)
      (le_trans h.P_le (le_trans inf_le_right h.A_normal))
    rw [h.A_sup, h.A_inf, Subgroup.card_bot, h.P_card, mul_one] at hh
    exact hh
  have hrel : A.relIndex (centD H t) = p := by
    have h1 := relIndex_mul_card_of_le' (H := A) (K := centD H t) h.A_le
    rw [hcardV, mul_comm (Nat.card ↥A) p] at h1
    exact Nat.mul_right_cancel (Nat.card_pos) h1
  have hNA_le_V : N ⊔ A ≤ centD H t := sup_le hNleV h.A_le
  have hdvd : A.relIndex (N ⊔ A) ∣ p := by
    have h1 := Subgroup.relIndex_mul_relIndex A (N ⊔ A) (centD H t) le_sup_right hNA_le_V
    rw [hrel] at h1; exact ⟨_, h1.symm⟩
  rcases h.prime.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
  · have hcard : Nat.card ↥(N ⊔ A) = Nat.card ↥A := by
      have h2 := relIndex_mul_card_of_le' (H := A) (K := N ⊔ A) le_sup_right
      rw [h1, one_mul] at h2; exact h2.symm
    have heq : A = N ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_right (le_of_eq hcard)
    rw [heq]; exact le_sup_left
  · exfalso
    have hcs := card_sup_mul_card_inf (H := A) (K := N) (le_trans hNleV h.A_normal)
    rw [sup_comm A N, inf_comm A N] at hcs
    have hcardNA : Nat.card ↥(N ⊔ A) = (A.relIndex (N ⊔ A)) * Nat.card ↥A :=
      (relIndex_mul_card_of_le' le_sup_right).symm
    rw [hcardNA, hp'] at hcs
    have hp_dvd : p ∣ Nat.card ↥A * Nat.card ↥N := by
      rw [← hcs]; exact dvd_mul_of_dvd_left (dvd_mul_right p (Nat.card ↥A)) _
    have hpdvdN : p ∣ Nat.card ↥N :=
      (h.prime.dvd_mul.mp hp_dvd).resolve_left (prop1_notDvdCardA h hPsyl)
    exact prop1_notDvdKg hFT h (dvd_trans hpdvdN (Subgroup.card_dvd_of_le inf_le_left))

/-- `[A,P]` is a normal complement of `C_A(P)` in `A` (App. I (5)(b)). -/
lemma prop1_NP (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : Design.Setup45A G H t W p P A)
    (hPsyl : IsSylowIn p P (twoPoint H t))
    (h4 : Step4Conc H t p P A) (h5 : Step5Conc H t p P A) :
    IsNormalComplementOf (Design.commSub A P) (A ⊓ Subgroup.centralizer (P : Set G)) A := by
  obtain ⟨ht2, htD, hodd, hcop, hsolv, hKg, hKappKset, hD_eq, hcardKg, hKg_le_D, hD_le_normKg⟩ :=
    prop1_prep hFT h
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hcyc : IsCyclic ↥P := isCyclic_of_prime_card h.P_card
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top P).mp hcyc
  have hgP : g ∈ P := hg ▸ Subgroup.mem_zpowers g
  have hord : orderOf g = p := by rw [← Nat.card_zpowers, hg, h.P_card]
  have hcent : Subgroup.centralizer ({g} : Set G) = Subgroup.centralizer (P : Set G) := by
    rw [← hg, Subgroup.zpowers_eq_closure]
    exact (Subgroup.centralizer_closure ({g} : Set G)).symm
  have hgV : g ∈ centD H t := le_trans h.P_le inf_le_right hgP
  have hnormA : NormalizedBy g A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (h.A_normal hgV) a).mp ha
  have hnotdvdA : ¬ p ∣ Nat.card ↥A := prop1_notDvdCardA h hPsyl
  have hcopA : Nat.Coprime (Nat.card ↥A) p := (h.prime.coprime_iff_not_dvd.mpr hnotdvdA).symm
  have hoddA : Odd (Nat.card ↥A) :=
    Odd.of_dvd_nat hodd
      (dvd_trans (Subgroup.card_dvd_of_le h.A_le) (Subgroup.card_dvd_of_le inf_le_left))
  have hsolvA : Group.IsSolvable ↥A := hFT ↥A hoddA
  have hCg_eq : Subgroup.centralizer ({g} : Set G) ⊓ A =
      A ⊓ Subgroup.centralizer (P : Set G) := by rw [hcent, inf_comm]
  have hcopF : Nat.Coprime (Kapp g A).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({g} : Set G) ⊓ A))) := by
    refine Nat.coprime_of_dvd (fun r hr h1 h2 => ?_)
    have hkr : (Kapp g A).ncard =
        (Subgroup.centralizer ({g} : Set G) ⊓ A).relIndex A := appI_kapp_ncard g A
    have hr1 : r ∣ (Subgroup.centralizer ({g} : Set G) ⊓ A).relIndex A := hkr ▸ h1
    have hCg_le_A : Subgroup.centralizer ({g} : Set G) ⊓ A ≤ A := inf_le_right
    have hCg_le_D : Subgroup.centralizer ({g} : Set G) ⊓ A ≤ twoPoint H t :=
      le_trans hCg_le_A (le_trans h.A_le inf_le_left)
    have hrvolD : r ∣ (Subgroup.centralizer ({g} : Set G) ⊓ A).relIndex (twoPoint H t) :=
      dvd_trans hr1 ⟨A.relIndex (twoPoint H t),
        (Subgroup.relIndex_mul_relIndex _ A (twoPoint H t) hCg_le_A
          (le_trans h.A_le inf_le_left)).symm⟩
    have hrvolD' : r ∣ (A ⊓ Subgroup.centralizer (P : Set G)).relIndex (twoPoint H t) :=
      hCg_eq ▸ hrvolD
    have hrdvdD : r ∣ Nat.card ↥(twoPoint H t) :=
      dvd_trans hrvolD ⟨Nat.card ↥(Subgroup.centralizer ({g} : Set G) ⊓ A),
        (relIndex_mul_card_of_le' hCg_le_D).symm⟩
    have hrdvdA : r ∣ Nat.card ↥A :=
      dvd_trans hr1 ⟨Nat.card ↥(Subgroup.centralizer ({g} : Set G) ⊓ A),
        (relIndex_mul_card_of_le' hCg_le_A).symm⟩
    have hrne : r ≠ p := fun heq => hnotdvdA (heq ▸ hrdvdA)
    have hnpi : ¬ Design.piSec4 H t p r := fun hpi => h5 r hpi hrvolD'
    have hrK : r ∣ (Kset (twoPoint H t) t).ncard := by
      by_contra hnr
      exact hnpi ⟨hr, hrdvdD, hrne, hnr⟩
    have hrCg : r ∣ Nat.card ↥(Subgroup.centralizer ({g} : Set G) ⊓ A) :=
      dvd_trans h2 (Subgroup.card_subgroup_dvd_card _)
    have hrC0 : r ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := hCg_eq ▸ hrCg
    exact (h4 r hr hrC0).2.2.2 hrK
  obtain ⟨K, hKset, hnc⟩ := appI_five_b h.prime hord hnormA hcopA hsolvA hcopF
  have hsub : Kapp g A ⊆ (K : Set G) := by rw [hKset]
  have hKcl : K = Subgroup.closure (Kapp g A) := by
    refine le_antisymm ?_ ((Subgroup.closure_le K).mpr hsub)
    intro x hx
    exact Subgroup.subset_closure (by rw [← hKset]; exact hx)
  have hcomm : Design.commSub A P = Subgroup.closure (Kapp g A) := by
    rw [Design.commSub, ← hg]
    exact commutator_zpowers_eq_closure_Kapp hnormA
  rw [hKcl, ← hcomm] at hnc
  rw [hCg_eq] at hnc
  exact hnc

/-- `⟨Kset D t⟩ ⊓ V ≤ [A,P]`. -/
lemma prop1_conj1 (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : Design.Setup45A G H t W p P A)
    (hPsyl : IsSylowIn p P (twoPoint H t))
    (h4 : Step4Conc H t p P A) (h5 : Step5Conc H t p P A) :
    Kgrp (twoPoint H t) t ⊓ centD H t ≤ Design.commSub A P := by
  obtain ⟨ht2, htD, hodd, hcop, hsolv, hKg, hKappKset, hD_eq, hcardKg, hKg_le_D, hD_le_normKg⟩ :=
    prop1_prep hFT h
  have hnc := prop1_NP hFT h hPsyl h4 h5
  set N : Subgroup G := Kgrp (twoPoint H t) t ⊓ centD H t with hNdef
  set Q0 : Subgroup G := Design.commSub A P with hQ0def
  set C0 : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hC0def
  have hNleA : N ≤ A := prop1_NleA hFT h hPsyl
  have hpKg : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥N → q ∣ (Kset (twoPoint H t) t).ncard := by
    intro q hq hqdvd
    have hdvdKg : q ∣ Nat.card ↥(Kgrp (twoPoint H t) t) :=
      dvd_trans hqdvd (Subgroup.card_dvd_of_le inf_le_left)
    rw [hKg] at hdvdKg
    have h := (appI_five_a (d := 2) Nat.prime_two h.invol htD hcop hsolv q hq).mp hdvdKg
    rwa [hKappKset] at h
  have hQ0_le_A : Q0 ≤ A := hnc.1
  have hA_normQ0 : A ≤ Subgroup.normalizer (Q0 : Set G) := hnc.2.1
  have hN_normQ0 : N ≤ Subgroup.normalizer (Q0 : Set G) := le_trans hNleA hA_normQ0
  have he_dvd_N : Q0.relIndex (N ⊔ Q0) ∣ Nat.card ↥N := by
    have h1 : Q0.relIndex (N ⊔ Q0) * Nat.card ↥Q0 = Nat.card ↥(N ⊔ Q0) :=
      relIndex_mul_card_of_le' le_sup_right
    have h2 : Nat.card ↥(Q0 ⊔ N) * Nat.card ↥(Q0 ⊓ N) = Nat.card ↥Q0 * Nat.card ↥N :=
      card_sup_mul_card_inf hN_normQ0
    rw [sup_comm Q0 N] at h2
    have h3 : Q0.relIndex (N ⊔ Q0) * (Nat.card ↥Q0 * Nat.card ↥(Q0 ⊓ N)) =
        Nat.card ↥Q0 * Nat.card ↥N := by
      rw [← mul_assoc, h1]; exact h2
    have h4 : Nat.card ↥Q0 * (Q0.relIndex (N ⊔ Q0) * Nat.card ↥(Q0 ⊓ N)) =
        Nat.card ↥Q0 * Nat.card ↥N := by
      rw [← h3]; ring
    exact ⟨Nat.card ↥(Q0 ⊓ N), (Nat.mul_left_cancel (Nat.card_pos) h4).symm⟩
  have hQ0A : Q0.relIndex A = Nat.card ↥C0 := by
    have hA_eq : Nat.card ↥A = Nat.card ↥Q0 * Nat.card ↥C0 := by
      have h2 : Nat.card ↥(Q0 ⊔ C0) * Nat.card ↥(Q0 ⊓ C0) = Nat.card ↥Q0 * Nat.card ↥C0 :=
        card_sup_mul_card_inf (le_trans inf_le_left hA_normQ0)
      rw [hnc.2.2.2, hnc.2.2.1, Subgroup.card_bot, mul_one] at h2
      exact h2
    have h1 := relIndex_mul_card_of_le' (H := Q0) (K := A) hQ0_le_A
    rw [hA_eq, mul_comm (Nat.card ↥Q0) (Nat.card ↥C0)] at h1
    exact Nat.mul_right_cancel (Nat.card_pos) h1
  have he_dvd_C : Q0.relIndex (N ⊔ Q0) ∣ Nat.card ↥C0 := by
    have hrel := Subgroup.relIndex_mul_relIndex Q0 (N ⊔ Q0) A le_sup_right
      (sup_le hNleA hQ0_le_A)
    rw [hQ0A] at hrel
    exact ⟨_, hrel.symm⟩
  have he : Q0.relIndex (N ⊔ Q0) = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqe⟩ := Nat.exists_prime_and_dvd hne
    have hqN : q ∣ Nat.card ↥N := dvd_trans hqe he_dvd_N
    have hqC : q ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
      rw [← hC0def]; exact dvd_trans hqe he_dvd_C
    exact (h4 q hq hqC).2.2.2 (hpKg q hq hqN)
  rw [Subgroup.relIndex_eq_one] at he
  exact le_sup_left.trans he

/-- `H ≤ N_G(K ⊔ L)` if `H` normalizes both `K` and `L`. -/
lemma prop1_le_normalizer_sup {K L H : Subgroup G}
    (hK : H ≤ Subgroup.normalizer (K : Set G))
    (hL : H ≤ Subgroup.normalizer (L : Set G)) :
    H ≤ Subgroup.normalizer ((K ⊔ L : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh x hx
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun y _ => h * y * h⁻¹ ∈ K ⊔ L) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyK | hyL
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hK hh) y).mp hyK)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hL hh) y).mp hyL)
  · rw [show h * 1 * h⁻¹ = 1 from by group]; exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [show h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) from by group]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [show h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ from by group]
    exact Subgroup.inv_mem _ hx

/-- **Peterfalvi I Ch. III §4 Prop. 1, step 6** (p.180): the last two clauses of `Prop1Conc`
(`Submission/Work/NormalComplement/NC4/Defs.lean`): with `D = twoPoint H t`, `V = centD H t`,
`Kg = Kgrp D t = ⟨Kset D t⟩` and `C = C_A(P) = A ⊓ C_G(P)`,

* `Kg ⊓ V ≤ [A,P]`, and
* `(Kg ⊔ [A,P]) ⊔ P` is a normal complement of `C` in `D`.

Route (the source's step 6, p.180):
* By step 5 (`h5 : Step5Conc`) `C` is Hall in `D`; by step 4 (`h4 : Step4Conc`) `C` is a
  `π`-group, and `V = A ⋊ P` with `A ⊴ V`, `A ⊓ P = ⊥`.
* App. I (5)(b) (`Work.NormalComplement.appI_five_b`, applied to `X = A` and `t` a generator of the
  cyclic group `P` of order `p`) gives that `[A,P]` is a normal complement of `C_A(P) = C` in `A`.
* Hence `(Kg ⊔ [A,P]) ⊔ P = Kg ⊔ (A ⊔ P) = Kg ⊔ V = D` (using §4 Lemma 1 (c)
  `Work.NormalComplement.sec4_one_c` for `D = Kg ⊔ V = Kg ⊔ A ⊔ P`), the intersection with `C`
  is trivial, and the subgroup is normal in `D`.
* `Kg ⊓ V ≤ [A,P]`: an element of `Kg ⊓ V` lies in `O_{π'}(A)` — here one uses that `C` is Hall in
  `D` (`h5`) and that `A`'s `π'`-part is `[A,P]` (the normal complement produced by App. I (5)(b)).
  The source writes this as `⟨K⟩ ∩ V ⊆ O_{π'}(A) = [A,P]`. -/
theorem prop1_concl (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hCC : Work.NormalComplement.ControlCorollaryProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    (h4 : Work.NormalComplement.S5K.Step4Conc H t p P A)
    (h5 : Work.NormalComplement.S5K.Step5Conc H t p P A) :
    Work.NormalComplement.Kgrp (Submission.Blueprint.twoPoint H t) t ⊓ Submission.Blueprint.centD H t
        ≤ Work.NormalComplement.Design.commSub A P ∧
      Work.NormalComplement.IsNormalComplementOf
        ((Work.NormalComplement.Kgrp (Submission.Blueprint.twoPoint H t) t ⊔
          Work.NormalComplement.Design.commSub A P) ⊔ P)
        (A ⊓ Subgroup.centralizer (P : Set G)) (Submission.Blueprint.twoPoint H t) := by
  obtain ⟨ht2, htD, hodd, hcop, hsolv, hKg, hKappKset, hD_eq, hcardKg, hKg_le_D, hD_le_normKg⟩ :=
    prop1_prep hFT h
  have hnc := prop1_NP hFT h hPsyl h4 h5
  have hconj1 := prop1_conj1 hFT h hPsyl h4 h5
  have hQ0_le_A : Design.commSub A P ≤ A := hnc.1
  have hA_normQ0 : A ≤ Subgroup.normalizer (Design.commSub A P : Set G) := hnc.2.1
  have hQ0_le_V : Design.commSub A P ≤ centD H t := le_trans hQ0_le_A h.A_le
  have hP_le_V : P ≤ centD H t := le_trans h.P_le inf_le_right
  have hP_le_D : P ≤ twoPoint H t := le_trans h.P_le (le_trans inf_le_left inf_le_right)
  have hB_le_V : Design.commSub A P ⊔ P ≤ centD H t := sup_le hQ0_le_V hP_le_V
  have hV_le_D : centD H t ≤ twoPoint H t := inf_le_left
  have hA_le_D : A ≤ twoPoint H t := le_trans h.A_le hV_le_D
  have hB_le_D : Design.commSub A P ⊔ P ≤ twoPoint H t := le_trans hB_le_V hV_le_D
  have hQ0P : Design.commSub A P ⊓ P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : x ∈ A ⊓ P := ⟨hQ0_le_A hx.1, hx.2⟩
    rw [h.A_inf] at h1
    exact Subgroup.mem_bot.mp h1
  -- `P` normalizes `[A,P]`
  have hP_normQ0 : P ≤ Subgroup.normalizer (Design.commSub A P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp q hq
    rw [Design.commSub, Subgroup.commutator_def] at hq
    refine Subgroup.closure_induction (p := fun y _ => p * y * p⁻¹ ∈ Design.commSub A P) ?_ ?_ ?_ ?_ hq
    · intro y hy
      obtain ⟨a, ha, p', hp', heq⟩ := hy
      rw [← heq]
      show p * ⁅a, p'⁆ * p⁻¹ ∈ ⁅A, P⁆
      refine Subgroup.subset_closure ⟨p * a * p⁻¹, ?_, p * p' * p⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (h.A_normal (le_trans h.P_le inf_le_right hp)) a).mp ha
      · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hp) p').mp hp'
      · exact (show p * ⁅a, p'⁆ * p⁻¹ = ⁅p * a * p⁻¹, p * p' * p⁻¹⁆ from by
          rw [commutatorElement_def]; group).symm
    · rw [show p * 1 * p⁻¹ = 1 from by group]; exact Subgroup.one_mem _
    · intro x y _ _ hx hy
      rw [show p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) from by group]
      exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      rw [show p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ from by group]
      exact Subgroup.inv_mem _ hx
  -- `A` normalizes `[A,P] ⊔ P`
  have hA_normB : A ≤ Subgroup.normalizer ((Design.commSub A P ⊔ P : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    rw [Subgroup.sup_eq_closure] at hb
    refine Subgroup.closure_induction (p := fun y _ =>
      a * y * a⁻¹ ∈ Design.commSub A P ⊔ P) ?_ ?_ ?_ ?_ hb
    · intro y hy
      rcases hy with hyQ | hyP
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hA_normQ0 ha) y).mp hyQ)
      · have hcomm : ⁅a, y⁆ ∈ Design.commSub A P := by
          show ⁅a, y⁆ ∈ ⁅A, P⁆
          exact Subgroup.commutator_mem_commutator ha hyP
        have heq : a * y * a⁻¹ = ⁅a, y⁆ * y := by rw [commutatorElement_def]; group
        rw [heq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hyP)
    · rw [show a * 1 * a⁻¹ = 1 from by group]; exact Subgroup.one_mem _
    · intro x y _ _ hx hy
      rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) from by group]
      exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ from by group]
      exact Subgroup.inv_mem _ hx
  have hP_normB : P ≤ Subgroup.normalizer ((Design.commSub A P ⊔ P : Subgroup G) : Set G) :=
    prop1_le_normalizer_sup hP_normQ0 Subgroup.le_normalizer
  have hV_normB : centD H t ≤
      Subgroup.normalizer ((Design.commSub A P ⊔ P : Subgroup G) : Set G) := by
    rw [← h.A_sup]
    exact sup_le hA_normB hP_normB
  have hV_normKg : centD H t ≤
      Subgroup.normalizer ((Kgrp (twoPoint H t) t : Subgroup G) : Set G) :=
    le_trans hV_le_D hD_le_normKg
  -- `⟨Kset D t⟩` normalizes `⟨Kset D t⟩ ⊔ ([A,P] ⊔ P)`
  have hKg_normQ : Kgrp (twoPoint H t) t ≤
      Subgroup.normalizer ((Kgrp (twoPoint H t) t ⊔ (Design.commSub A P ⊔ P) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk q hq
    rw [Subgroup.sup_eq_closure] at hq
    refine Subgroup.closure_induction (p := fun y _ =>
      k * y * k⁻¹ ∈ Kgrp (twoPoint H t) t ⊔ (Design.commSub A P ⊔ P)) ?_ ?_ ?_ ?_ hq
    · intro y hy
      rcases hy with hyK | hyB
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) y).mp hyK)
      · have hcomm : ⁅k, y⁆ ∈ Kgrp (twoPoint H t) t := by
          have hmem : ⁅k, y⁆ ∈
              ⁅(Kgrp (twoPoint H t) t : Subgroup G), (Design.commSub A P ⊔ P : Subgroup G)⁆ :=
            Subgroup.commutator_mem_commutator hk hyB
          have hle : ⁅(Kgrp (twoPoint H t) t : Subgroup G), (Design.commSub A P ⊔ P : Subgroup G)⁆ ≤
              Kgrp (twoPoint H t) t := by
            rw [Subgroup.commutator_le]
            intro k' hk' b hb
            have hbD : b ∈ twoPoint H t := hB_le_D hb
            have h1 : b * k'⁻¹ * b⁻¹ ∈ Kgrp (twoPoint H t) t :=
              (Subgroup.mem_normalizer_iff.mp (hD_le_normKg hbD) k'⁻¹).mp (Subgroup.inv_mem _ hk')
            rw [commutatorElement_def,
              show k' * b * k'⁻¹ * b⁻¹ = k' * (b * k'⁻¹ * b⁻¹) from by group]
            exact Subgroup.mul_mem _ hk' h1
          exact hle hmem
        have heq : k * y * k⁻¹ = ⁅k, y⁆ * y := by rw [commutatorElement_def]; group
        rw [heq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hyB)
    · rw [show k * 1 * k⁻¹ = 1 from by group]; exact Subgroup.one_mem _
    · intro x y _ _ hx hy
      rw [show k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) from by group]
      exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      rw [show k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ from by group]
      exact Subgroup.inv_mem _ hx
  set C0 : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hC0def
  set Q : Subgroup G := (Kgrp (twoPoint H t) t ⊔ Design.commSub A P) ⊔ P with hQdef
  have hQ_eq : Q = Kgrp (twoPoint H t) t ⊔ (Design.commSub A P ⊔ P) := by
    rw [hQdef, sup_assoc]
  have hQ_le_D : Q ≤ twoPoint H t :=
    sup_le (sup_le hKg_le_D (le_trans hQ0_le_A (le_trans h.A_le inf_le_left))) hP_le_D
  have hD_norm_Q : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) := by
    have hle : Kgrp (twoPoint H t) t ⊔ centD H t ≤ Subgroup.normalizer (Q : Set G) := by
      rw [hQ_eq]
      exact sup_le hKg_normQ (prop1_le_normalizer_sup hV_normKg hV_normB)
    rwa [← hD_eq] at hle
  have hQsupC : Q ⊔ C0 = twoPoint H t := by
    refine le_antisymm ?_ ?_
    · exact sup_le hQ_le_D (le_trans inf_le_left (le_trans h.A_le inf_le_left))
    · rw [hD_eq]
      refine sup_le (le_trans le_sup_left (le_trans le_sup_left le_sup_left)) ?_
      rw [← h.A_sup, ← hnc.2.2.2]
      exact sup_le (sup_le (le_trans le_sup_right (le_trans le_sup_left le_sup_left))
        le_sup_right) (le_trans le_sup_right le_sup_left)
  have hN_eq : Kgrp (twoPoint H t) t ⊓ (Design.commSub A P ⊔ P) =
      Kgrp (twoPoint H t) t ⊓ centD H t := by
    refine le_antisymm ?_ ?_
    · exact le_inf inf_le_left (le_trans inf_le_right hB_le_V)
    · exact le_inf inf_le_left (le_trans hconj1 le_sup_left)
  have hcardB : Nat.card ↥(Design.commSub A P ⊔ P) = Nat.card ↥(Design.commSub A P) * p := by
    have h1 := card_sup_mul_card_inf (H := Design.commSub A P) (K := P) hP_normQ0
    rw [hQ0P, Subgroup.card_bot, mul_one, h.P_card] at h1
    exact h1
  have hcardA : Nat.card ↥A = Nat.card ↥(Design.commSub A P) * Nat.card ↥C0 := by
    have h1 := card_sup_mul_card_inf (H := Design.commSub A P) (K := C0)
      (le_trans inf_le_left hA_normQ0)
    rw [hnc.2.2.2, hnc.2.2.1, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hcardV : Nat.card ↥(centD H t) = Nat.card ↥A * p := by
    have h1 := card_sup_mul_card_inf (H := A) (K := P)
      (le_trans h.P_le (le_trans inf_le_right h.A_normal))
    rw [h.A_sup, h.A_inf, Subgroup.card_bot, h.P_card, mul_one] at h1
    exact h1
  have hcardD : Nat.card ↥(twoPoint H t) = (Kset (twoPoint H t) t).ncard * Nat.card ↥(centD H t) := by
    have h2 : (centD H t).relIndex (twoPoint H t) = (Kset (twoPoint H t) t).ncard := by
      have h3 : (Kapp t (twoPoint H t)).ncard = (centD H t).relIndex (twoPoint H t) := by
        rw [appI_kapp_ncard, centD, inf_comm]
        rfl
      rw [← hKappKset, h3]
    have h1 := relIndex_mul_card_of_le' (H := centD H t) (K := twoPoint H t) inf_le_left
    rw [h2] at h1; exact h1.symm
  have hBC : Nat.card ↥(Design.commSub A P ⊔ P) * Nat.card ↥C0 = Nat.card ↥(centD H t) := by
    rw [hcardB, hcardV, hcardA]; ring
  have hQN : Nat.card ↥Q * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t) =
      Nat.card ↥(Kgrp (twoPoint H t) t) * Nat.card ↥(Design.commSub A P ⊔ P) := by
    rw [hQdef, sup_assoc, ← hN_eq]
    exact card_sup_mul_card_inf (le_trans hB_le_D hD_le_normKg)
  have hkey : Nat.card ↥Q * Nat.card ↥C0 * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t) =
      Nat.card ↥(twoPoint H t) * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t) := by
    calc Nat.card ↥Q * Nat.card ↥C0 * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t)
        = Nat.card ↥Q * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t) * Nat.card ↥C0 := by ring
      _ = Nat.card ↥(Kgrp (twoPoint H t) t) * Nat.card ↥(Design.commSub A P ⊔ P) *
            Nat.card ↥C0 := by rw [hQN]
      _ = ((Kset (twoPoint H t) t).ncard * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t)) *
            Nat.card ↥(Design.commSub A P ⊔ P) * Nat.card ↥C0 := by rw [hcardKg]
      _ = (Kset (twoPoint H t) t).ncard *
            (Nat.card ↥(Design.commSub A P ⊔ P) * Nat.card ↥C0) *
            Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t) := by ring
      _ = (Kset (twoPoint H t) t).ncard * Nat.card ↥(centD H t) *
            Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t) := by rw [hBC]
      _ = Nat.card ↥(twoPoint H t) * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ centD H t) := by rw [hcardD]
  have hcardQC : Nat.card ↥Q * Nat.card ↥C0 = Nat.card ↥(twoPoint H t) :=
    Nat.mul_right_cancel (Nat.card_pos) hkey
  have hC0_le_D : C0 ≤ twoPoint H t := le_trans inf_le_left hA_le_D
  have hC0_normQ : C0 ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans hC0_le_D hD_norm_Q
  have hQinfC : Q ⊓ C0 = ⊥ := by
    have hsup := card_sup_mul_card_inf (H := Q) (K := C0) hC0_normQ
    rw [hQsupC, hcardQC] at hsup
    have h1 : Nat.card ↥(twoPoint H t) * Nat.card ↥(Q ⊓ C0) = Nat.card ↥(twoPoint H t) * 1 := by
      rw [mul_one]; exact hsup
    exact Subgroup.card_eq_one.mp (Nat.mul_left_cancel (Nat.card_pos) h1)
  rw [IsNormalComplementOf]
  exact ⟨hconj1, hQ_le_D, hD_norm_Q, hQinfC, hQsupC⟩

end Work.NormalComplement.S5K
