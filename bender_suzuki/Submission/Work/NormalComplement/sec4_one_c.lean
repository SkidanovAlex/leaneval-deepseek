import Mathlib
import Submission.Work.NormalComplement._design.Vocab
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_five_a
import Submission.Work.NormalComplement.appI_five_c_prime
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.sec4_c_normalizer_eq
import Submission.Work.NormalComplement.sec4_c_normalizes

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Submission.Blueprint
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [Finite G]

/-- An element of order `2` is its own inverse (`t * t = 1`). -/
lemma twoPoint_mul_self {t : G} (ht : orderOf t = 2) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rw [ht] at h
  simpa [pow_two] using h

/-- `t` of order `2` normalises `D = twoPoint H t`. -/
lemma twoPoint_normalizedBy {H : Subgroup G} {t : G} (ht2 : t * t = 1) :
    NormalizedBy t (twoPoint H t) := by
  intro x hx
  obtain ⟨hxH, hxconj⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hhH, hhx⟩ := Subgroup.mem_map.mp hxconj
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hhx
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hmem : t * x * t⁻¹ = h := by
      rw [← hhx, hti]
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by rw [ht2]; simp
    rw [hmem]; exact hhH
  · exact Subgroup.mem_map.mpr
      ⟨x, hxH, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

/-- **Peterfalvi I Ch. III §4 Lemma 1 (c)** (p.179), in the design vocabulary
(`Submission.Work.NormalComplement._design.Vocab`, `D = twoPoint H t`, `Kgrp D t = ⟨J(D,t)⟩`): with
`Setup45A G H t W p P A`, one has `N_D(P) = C_A(P) · P` and `D = ⟨K⟩A ⋊ P`.

Route (the paper): `|D|` is odd (`IsStronglyEmbedded` at `t ∉ H`) hence `↥D` is solvable by `hFT`;
App. I (5)(c) (`Work.NormalComplement.appI_five_c_prime` with `X = D`, `p` prime, `P ≤ V` and `P`
fixed-point-free on `K`) gives `N_D(P) ≤ V`; with `V = A ⋊ P` and `A ⊴ V`, `N_V(P) = C_A(P)·P`.
App. I (4) (`Work.NormalComplement.appI_four`) gives `⟨K⟩ ⊴ D` and `D = ⟨K⟩V = ⟨K⟩AP`; `p ∤ |K|`
(`C_K(P) = 1` from fixed-point-freeness) and App. I (5)(a)
(`Work.NormalComplement.appI_five_a`, with `p ∤ |K|`) gives `p ∤ |⟨K⟩|`; since `P ⊓ A = ⊥` and
`p ∤ |A|` (A ≤ V = C_D(t) and P fixed-point-free on K force `p ∤ |A|` as `|A| ∣ |D|`), one gets
`p ∤ |⟨K⟩A|`, so `⟨K⟩A ⊓ P = ⊥` and `D = ⟨K⟩A ⋊ P`. -/
theorem sec4_one_c (hFT : Submission.Blueprint.FeitThompsonProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G} (h : Work.NormalComplement.Design.Setup45A G H t W p P A) :
    Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G) =
        (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P ∧
      Submission.Blueprint.twoPoint H t ≤
        Subgroup.normalizer ((Work.NormalComplement.Kgrp (Submission.Blueprint.twoPoint H t) t ⊔ A :
          Subgroup G) : Set G) ∧
      (Work.NormalComplement.Kgrp (Submission.Blueprint.twoPoint H t) t ⊔ A) ⊓ P = ⊥ ∧
      (Work.NormalComplement.Kgrp (Submission.Blueprint.twoPoint H t) t ⊔ A) ⊔ P =
        Submission.Blueprint.twoPoint H t := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  -- ## Basic facts about `D = twoPoint H t`, `t`, `K = Kset D t`.
  have ht2 : t * t = 1 := twoPoint_mul_self h.invol
  have htD : NormalizedBy t (twoPoint H t) := twoPoint_normalizedBy ht2
  have hodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have hcop : (Nat.card ↥(twoPoint H t)).Coprime 2 := Nat.coprime_two_right.mpr hodd
  have hsolv : Group.IsSolvable ↥(twoPoint H t) := hFT ↥(twoPoint H t) hodd
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two h.invol htD hcop).2 rfl).1
  have hKg : Kgrp (twoPoint H t) t = Subgroup.closure (Kapp t (twoPoint H t)) := by
    rw [Kgrp, ← hKappKset]
  have hfour := appI_four (d := 2) Nat.prime_two h.invol htD hcop
  have hV_le_D : centD H t ≤ twoPoint H t := inf_le_left
  have hcen_comm : Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t = centD H t := by
    rw [centD, inf_comm]
  have hD_eq : twoPoint H t = Kgrp (twoPoint H t) t ⊔ centD H t := by
    rw [hKg, ← hcen_comm]
    exact hfour.2.2.2.1.symm
  -- `P` is a `p`-group of order `p`, sits in `V = C_D(t)`.
  have hP_le_V : P ≤ centD H t := le_trans h.P_le inf_le_right
  have hPp : IsPGroup p ↥P := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [pow_one]; exact h.P_card⟩
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h.P_card] at h1
    exact h.prime.ne_one h1
  have hP_fixX : P ≤ fixX t (twoPoint H t) := by
    have : P ≤ Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t := by
      rw [hcen_comm]; exact hP_le_V
    exact this
  -- Fixed point freeness restated for `Kapp` (which coincides with `Kset`).
  have hfpfKapp : ∀ k ∈ Kapp t (twoPoint H t), (∀ u ∈ P, u * k * u⁻¹ = k) → k = 1 :=
    kapp_fixed_eq_one_of_fpf hP_ne_bot (fun u hu hu1 k hk hfix => by
      refine h.P_fpf u hu hu1 k ?_ hfix
      rwa [hKappKset] at hk)
  -- `N_D(P) ≤ V` (Peterfalvi App. I (5)(c), first part).
  have hND_le_V : twoPoint H t ⊓ Subgroup.normalizer (P : Set G) ≤ centD H t := by
    intro z hz
    obtain ⟨hzD, hzN⟩ := Subgroup.mem_inf.mp hz
    have hz' := mem_fixX_of_normalizes (d := 2) Nat.prime_two h.invol htD hcop hsolv h.prime
      hP_fixX hPp hfpfKapp z hzD (fun u hu => (Subgroup.mem_normalizer_iff.mp hzN u).mp hu)
    have : z ∈ Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t := hz'
    rw [hcen_comm] at this
    exact this
  -- `D` normalises `Kgrp D t` (App. I (4)).
  have hK_norm : twoPoint H t ≤ Subgroup.normalizer ((Kgrp (twoPoint H t) t : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hxD k hk
    have hk' : k ∈ Subgroup.closure (Kapp t (twoPoint H t)) := by rw [← hKg]; exact hk
    have hh := hfour.2.2.1 x hxD k hk'
    rw [hKg]
    exact hh
  -- ## The four conjuncts.
  have hconj1 : twoPoint H t ⊓ Subgroup.normalizer (P : Set G) =
      (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P :=
    sec4_c_normalizer_eq hV_le_D h.A_le h.A_normal h.A_inf h.A_sup hP_le_V hND_le_V
  have hDV' : twoPoint H t = centD H t ⊔ Kgrp (twoPoint H t) t := by
    rw [sup_comm]; exact hD_eq
  have hconj2 : twoPoint H t ≤
      Subgroup.normalizer ((Kgrp (twoPoint H t) t ⊔ A : Subgroup G) : Set G) :=
    sec4_c_normalizes hK_norm hDV' hV_le_D h.A_normal
  have hconj4 : (Kgrp (twoPoint H t) t ⊔ A) ⊔ P = twoPoint H t := by
    have h1 := sup_assoc (Kgrp (twoPoint H t) t) A P
    rw [h1, h.A_sup]
    exact hD_eq.symm
  have hconj3 : (Kgrp (twoPoint H t) t ⊔ A) ⊓ P = ⊥ := by
    -- ## Cardinality bookkeeping (Peterfalvi's `|⟨K⟩A|_p = |A|_p < |D|_p`).
    -- Product formula for `⟨K⟩` and `A`.
    have hprod1 : Nat.card ↥(Kgrp (twoPoint H t) t ⊔ A) *
          Nat.card ↥(Kgrp (twoPoint H t) t ⊓ A)
        = Nat.card ↥(Kgrp (twoPoint H t) t) * Nat.card ↥A :=
      card_sup_mul_card_inf (le_trans (le_trans h.A_le hV_le_D) hK_norm)
    -- Product formula for `⟨K⟩A` and `P`.
    have hprod2 : Nat.card ↥(twoPoint H t) *
          Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P)
        = Nat.card ↥(Kgrp (twoPoint H t) t ⊔ A) * Nat.card ↥P := by
      have hh := card_sup_mul_card_inf (H := Kgrp (twoPoint H t) t ⊔ A) (K := P)
        (le_trans (le_trans hP_le_V hV_le_D) hconj2)
      rw [hconj4] at hh
      exact hh
    -- `|V| = |A| * p`.
    have hcardV : Nat.card ↥(centD H t) = Nat.card ↥A * Nat.card ↥P := by
      have hh := card_sup_mul_card_inf (H := A) (K := P) (le_trans hP_le_V h.A_normal)
      rw [h.A_sup, h.A_inf, Subgroup.card_bot, mul_one] at hh
      exact hh
    -- `|D| = |V| * |Kapp t D|`.
    have hcardD : Nat.card ↥(twoPoint H t)
        = Nat.card ↥(centD H t) * (Kapp t (twoPoint H t)).ncard := by
      have hci := Subgroup.card_mul_index ((centD H t).subgroupOf (twoPoint H t))
      have hcard_sub : Nat.card ↥((centD H t).subgroupOf (twoPoint H t))
          = Nat.card ↥(centD H t) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_D).toEquiv
      have hidx : ((centD H t).subgroupOf (twoPoint H t)).index
          = (Kapp t (twoPoint H t)).ncard := by
        have h1 := (appI_one (d := 2) Nat.prime_two h.invol htD hcop).1
        rw [h1, ← hcen_comm]
      rw [hcard_sub, hidx] at hci
      exact hci.symm
    -- `p ∤ |K|` (orbit counting) and `p ∤ |⟨K⟩|` (App. I (5)(a)).
    have hps : ¬ p ∣ (Kapp t (twoPoint H t)).ncard :=
      not_dvd_ncard_Kapp h.prime hP_fixX hPp hfpfKapp
    have hpKg : ¬ p ∣ Nat.card ↥(Kgrp (twoPoint H t) t) := by
      rw [hKg]
      exact not_dvd_card_closureKapp h.prime Nat.prime_two h.invol htD hcop hsolv
        hP_fixX hPp hfpfKapp
    -- `|⟨K⟩A| = u * |A|` with `p ∤ u`.
    have ht0dvd : Nat.card ↥(Kgrp (twoPoint H t) t ⊓ A) ∣ Nat.card ↥(Kgrp (twoPoint H t) t) :=
      Subgroup.card_dvd_of_le inf_le_left
    set u : ℕ := Nat.card ↥(Kgrp (twoPoint H t) t) / Nat.card ↥(Kgrp (twoPoint H t) t ⊓ A)
      with hu_def
    have hu : u * Nat.card ↥(Kgrp (twoPoint H t) t ⊓ A) = Nat.card ↥(Kgrp (twoPoint H t) t) :=
      Nat.div_mul_cancel ht0dvd
    have hpu : ¬ p ∣ u := fun hd => hpKg (hu ▸ dvd_mul_of_dvd_left hd _)
    have hk_eq : Nat.card ↥(Kgrp (twoPoint H t) t ⊔ A) = u * Nat.card ↥A := by
      refine Nat.mul_right_cancel (m := Nat.card ↥(Kgrp (twoPoint H t) t ⊓ A))
        (Nat.card_pos) ?_
      rw [hprod1, ← hu]
      ring
    -- The counting identity `|K| * |⟨K⟩A ⊓ P| = |K| * u` (cancelling `|V|` from `hprod2`).
    have hmain : (Kapp t (twoPoint H t)).ncard *
          Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P) = u := by
      have h2 : Nat.card ↥(centD H t) *
            ((Kapp t (twoPoint H t)).ncard *
              Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P))
          = Nat.card ↥(centD H t) * u := by
        calc Nat.card ↥(centD H t) *
              ((Kapp t (twoPoint H t)).ncard * Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P))
            = (Nat.card ↥(centD H t) * (Kapp t (twoPoint H t)).ncard) *
                Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P) := by ring
          _ = Nat.card ↥(twoPoint H t) *
                Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P) := by rw [← hcardD]
          _ = Nat.card ↥(Kgrp (twoPoint H t) t ⊔ A) * Nat.card ↥P := hprod2
          _ = (u * Nat.card ↥A) * Nat.card ↥P := by rw [← hk_eq]
          _ = u * (Nat.card ↥A * Nat.card ↥P) := by ring
          _ = u * Nat.card ↥(centD H t) := by rw [← hcardV]
          _ = Nat.card ↥(centD H t) * u := by ring
      exact Nat.mul_left_cancel (Nat.card_pos) h2
    -- `x = |⟨K⟩A ⊓ P|` divides `p` but not `u`, hence `x = 1`.
    have hxu : Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P) ∣ u :=
      ⟨(Kapp t (twoPoint H t)).ncard, by rw [mul_comm]; exact hmain.symm⟩
    have hpx : ¬ p ∣ Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P) :=
      fun hd => hpu (dvd_trans hd hxu)
    have hxp : Nat.card ↥((Kgrp (twoPoint H t) t ⊔ A) ⊓ P) ∣ p := by
      rw [← h.P_card]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime h.prime).mp hxp with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (by rw [h1]) hpx
  exact ⟨hconj1, hconj2, hconj3, hconj4⟩

end Work.NormalComplement
