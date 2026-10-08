import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.NC4.Defs
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.S5K.sec2_lemma1_w2
import Submission.Work.NormalComplement.S5K.prop2cd_w2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.S5K

variable {G : Type} [Group G] [Finite G]

/-! ## General helpers -/

/-- If `B ⊴ E` (`E ≤ N_G(B)`), `P ≤ E` is abelian and `E = B ⊔ P`, then `⁅E,E⁆ ≤ B`
(the quotient `E/B ≅ P` is abelian). -/
lemma commutator_le_of_sup_eq_of_comm {B P E : Subgroup G}
    (hN : B ⊔ P ≤ Subgroup.normalizer (B : Set G))
    (hcomm : ∀ u ∈ P, ∀ v ∈ P, u * v = v * u) (hsup : B ⊔ P = E) :
    ⁅E, E⁆ ≤ B := by
  rw [← hsup, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, hx, u, hu, rfl⟩ :=
    NC4.exists_mul_mem_of_sup_eq (E := B ⊔ P) (S := B) (T := P) (fun _ hx => Subgroup.mem_sup_left hx) (fun _ hx => Subgroup.mem_sup_right hx)
      rfl hN a ha
  obtain ⟨y, hy, v, hv, rfl⟩ :=
    NC4.exists_mul_mem_of_sup_eq (E := B ⊔ P) (S := B) (T := P) (fun _ hx => Subgroup.mem_sup_left hx) (fun _ hx => Subgroup.mem_sup_right hx)
      rfl hN b hb
  have hxu : u * y * u⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right hu)) y).mp hy
  have hvx : v * x⁻¹ * v⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right hv)) x⁻¹).mp (B.inv_mem hx)
  have hgen : ⁅x * u, y * v⁆
      = x * (u * y * u⁻¹) * (u * v * u⁻¹ * v⁻¹) * (v * x⁻¹ * v⁻¹) * y⁻¹ := by
    rw [commutatorElement_def]; group
  have huv : u * v * u⁻¹ * v⁻¹ = 1 := by rw [hcomm u hu v hv]; group
  rw [hgen, huv]
  simp only [mul_one]
  exact B.mul_mem (B.mul_mem (B.mul_mem hx hxu) hvx) (B.inv_mem hy)

/-- `O^p(W)`, as a set, is the closure of the `p'`-elements of `W`. -/
lemma pResidual_eq_closure (p : ℕ) (W : Subgroup G) :
    Work.Grun.pResidual p W = Subgroup.closure {x : G | x ∈ W ∧ ¬ p ∣ orderOf x} := by
  unfold Work.Grun.pResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hxW, hx⟩
    exact ⟨⟨x, hxW⟩, hx, rfl⟩

/-- `O^p` is monotone in the subgroup. -/
lemma pResidual_mono (p : ℕ) {W H : Subgroup G} (h : W ≤ H) :
    Work.Grun.pResidual p W ≤ Work.Grun.pResidual p H := by
  rw [pResidual_eq_closure p W, pResidual_eq_closure p H]
  exact Subgroup.closure_mono (fun x hx => ⟨h hx.1, hx.2⟩)

/-- A `p`-subgroup `U ≤ X` has order dividing the order of a `p`-Sylow of `X`. -/
lemma card_dvd_card_of_isPGroup_of_isSylowIn {p : ℕ} (hp : p.Prime) {U P X : Subgroup G}
    (hUX : U ≤ X) (hU : IsPGroup p U) (hP : IsSylowIn p P X) : Nat.card ↥U ∣ Nat.card ↥P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have h1 : Nat.card ↥U ∣ Nat.card ↥X := Subgroup.card_dvd_of_le hUX
  have h2 : Nat.card ↥X = Nat.card ↥P * P.relIndex X := by
    rw [mul_comm]
    exact (relIndex_mul_card_of_le' hP.2.1).symm
  have h3 : p ^ k ∣ Nat.card ↥P * P.relIndex X := by rw [← h2, ← hk]; exact h1
  have h4 : Nat.Coprime (p ^ k) (P.relIndex X) :=
    Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.mpr hP.2.2)
  rw [hk]
  exact h4.dvd_of_dvd_mul_right h3

/-- Modular law for subgroups: if `P ≤ W` and `B ⊔ P ≤ N_G(B)`, then
`W ⊓ (B ⊔ P) = (W ⊓ B) ⊔ P`. -/
lemma inf_sup_eq_sup_inf_of_le {B P W : Subgroup G}
    (hPW : P ≤ W) (hN : B ⊔ P ≤ Subgroup.normalizer (B : Set G)) :
    W ⊓ (B ⊔ P) = (W ⊓ B) ⊔ P := by
  refine le_antisymm ?_ (le_inf (sup_le inf_le_left hPW)
    (sup_le (fun x hx => Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).2)
      (fun x hx => Subgroup.mem_sup_right hx)))
  intro x hx
  obtain ⟨hxW, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨b, hbB, u, huP, hxu⟩ := NC4.exists_mul_mem_of_sup_eq (E := B ⊔ P) (S := B) (T := P)
    (fun _ hx => Subgroup.mem_sup_left hx) (fun _ hx => Subgroup.mem_sup_right hx) rfl hN x hxB
  have hbW : b ∈ W := by
    have hb : b = x * u⁻¹ := by rw [hxu]; group
    rw [hb]
    exact W.mul_mem hxW (W.inv_mem (hPW huP))
  rw [hxu]
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hbW, hbB⟩) huP

/-- **Peterfalvi I Ch. III §4 Lemma 1 (d)** (p.179): `P` is a `p`-Sylow subgroup of
`D = twoPoint H t`, and `E = Egrp H t W = W ⊓ D` equals `E' ⋊ P` with `E' = ⁅E,E⁆`. -/
theorem lemma1d (hFT : Submission.Blueprint.FeitThompsonProp)
    (hTrans : Work.NormalComplement.TransferProp)
    (hStrat : Work.NormalComplement.StrategyProp)
    (hS2 : Work.NormalComplement.Section2Prop)
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (hKinv : Work.NormalComplement.KInvariantUnderD H t)
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A) :
    Work.NormalComplement.NC4.Lemma1dConc H t W p P A := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  -- ## standing facts
  have hDleH : twoPoint H t ≤ H :=
    (le_sup_right : twoPoint H t ≤ W ⊔ twoPoint H t).trans (le_of_eq h.sup)
  have hPleE : P ≤ Design.Egrp H t W := h.P_le.trans inf_le_left
  have hPleD : P ≤ twoPoint H t := hPleE.trans inf_le_right
  have hPleV : P ≤ centD H t := le_trans h.P_le inf_le_right
  have hPleW : P ≤ W := hPleE.trans inf_le_left
  have hAleV : A ≤ centD H t := h.A_le
  have hVleD : centD H t ≤ twoPoint H t := inf_le_left
  have hAleD : A ≤ twoPoint H t := hAleV.trans hVleD
  have hVnormA : centD H t ≤ Subgroup.normalizer (A : Set G) := h.A_normal
  have hPp : IsPGroup p ↥P := by
    rw [IsPGroup.iff_card]; exact ⟨1, by rw [pow_one]; exact h.P_card⟩
  have hPne : P ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥P = 1 := by rw [hb]; exact Subgroup.card_bot
    rw [h.P_card] at h1
    exact h.prime.ne_one h1
  have hPcomm : ∀ u ∈ P, ∀ v ∈ P, u * v = v * u := by
    haveI hcyc : IsCyclic ↥P := isCyclic_of_prime_card h.P_card
    letI : CommGroup ↥P := hcyc.commGroup
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm (⟨u, hu⟩ : ↥P) (⟨v, hv⟩ : ↥P))
  -- ## §4 Lemma 1 (c)
  obtain ⟨hc1, hc2, hc3, hc4⟩ := sec4_one_c hFT h
  -- ## §2 Lemma 1 (proved; here in the `sec4_P2d`-world port)
  obtain ⟨hs2_K, -, hs2_fpf⟩ := Work.NormalComplement.sec2_lemma1_w2 hFT h.toSetup3
  -- ## `E'`
  have hE'leW : Design.Ecomm H t W ≤ W :=
    (Subgroup.commutator_le_self (Design.Egrp H t W)).trans inf_le_left
  have hKg_le : Work.NormalComplement.Kgrp (twoPoint H t) t ≤ Design.Ecomm H t W := by
    rw [Work.NormalComplement.Kgrp]
    exact (Subgroup.closure_le _).mpr hs2_K
  have hKgW : Work.NormalComplement.Kgrp (twoPoint H t) t ≤ W := hKg_le.trans hE'leW
  -- ## `D ≤ N(⟨K⟩)` (App. I (4))
  have htD : NormalizedBy t (twoPoint H t) := twoPoint_normalizedBy (twoPoint_mul_self h.invol)
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have hcopD : Nat.Coprime (Nat.card ↥(twoPoint H t)) 2 := Nat.coprime_two_right.mpr hoddD
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two h.invol htD hcopD).2 rfl).1
  have hfour := appI_four (d := 2) Nat.prime_two h.invol htD hcopD
  have hDnormKg : twoPoint H t ≤
      Subgroup.normalizer ((Work.NormalComplement.Kgrp (twoPoint H t) t : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr ?_
    intro x hx k hk
    rw [Work.NormalComplement.Kgrp, ← hKappKset] at hk ⊢
    exact hfour.2.2.1 x hx k hk
  -- ## the pair `B = ⟨K⟩A`, `P` with `D = B ⋊ P`
  set B : Subgroup G := Work.NormalComplement.Kgrp (twoPoint H t) t ⊔ A with hB
  have hBsup : B ⊔ P = twoPoint H t := by rw [hB]; exact hc4
  have hBinf : B ⊓ P = ⊥ := by rw [hB]; exact hc3
  have hBnorm : twoPoint H t ≤ Subgroup.normalizer (B : Set G) := by rw [hB]; exact hc2
  have hBnormP : P ≤ Subgroup.normalizer (B : Set G) := hPleD.trans hBnorm
  have hBleD : B ≤ twoPoint H t := hBsup ▸ le_sup_left
  have hcardD : Nat.card ↥B * p = Nat.card ↥(twoPoint H t) := by
    have hh := card_sup_mul_card_inf (H := B) (K := P) hBnormP
    rw [hBsup, hBinf, Subgroup.card_bot, mul_one, h.P_card] at hh
    exact hh.symm
  have hBrel : B.relIndex (twoPoint H t) = p := by
    have hh := relIndex_mul_card_of_le' hBleD
    have hh2 : B.relIndex (twoPoint H t) * Nat.card ↥B = p * Nat.card ↥B := by
      rw [hh, ← hcardD, mul_comm p]
    exact Nat.mul_right_cancel Nat.card_pos hh2
  have hcomB : ⁅twoPoint H t, twoPoint H t⁆ ≤ B :=
    commutator_le_of_sup_eq_of_comm (B := B) (P := P) (E := twoPoint H t)
      (hBsup ▸ hBnorm) hPcomm hBsup
  -- ## the identity `E = (W ⊓ B) ⋊ P`
  have hEq : Design.Egrp H t W = (W ⊓ B) ⊔ P := by
    show W ⊓ twoPoint H t = (W ⊓ B) ⊔ P
    rw [← hBsup]
    exact inf_sup_eq_sup_inf_of_le (B := B) (P := P) (W := W) hPleW (hBsup ▸ hBnorm)
  -- ## an element `k ≠ 1` of `K` centralised by `A`
  have hck : ∃ k ∈ Design.CK H t A, k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Design.CK H t A ⊆ ({1} : Set G) := fun x hx => by simpa using hcon x hx
    have h1 : (Design.CK H t A).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard hsub (Set.finite_singleton 1))
        (le_of_eq (Set.ncard_singleton 1))
    rw [h.A_CK] at h1
    have h2 : 3 ≤ 2 ^ p := by
      calc (3 : ℕ) ≤ 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h.prime.two_le
    omega
  -- ## the first conjunct: `P` is a `p`-Sylow of `D`
  have hPsyl : IsSylowIn p P (twoPoint H t) := by
    have hpD : p ∣ Nat.card ↥(H ⊓ twoPoint H t) := by
      rw [inf_eq_right.mpr hDleH, ← h.P_card]
      exact Subgroup.card_dvd_of_le hPleD
    rcases hS2 G h.sit H h.se t h.invol h.notMem H le_rfl Subgroup.le_normalizer
        (sup_eq_left.mpr hDleH) hKinv p h.prime hpD with
      hpc | ⟨P', hP'syl₀, hP'leV, hP'fpf, -⟩
    · -- Case 1: `D` is `p`-control in `H`; transfer and minimality contradict each other.
      exfalso
      obtain ⟨y, hyP, hy1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hPne
      have hyord : orderOf y = p := by
        have hdv : orderOf y ∣ Nat.card ↥P := Subgroup.orderOf_dvd_natCard P hyP
        rw [h.P_card] at hdv
        rcases (Nat.dvd_prime h.prime).mp hdv with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hy1
        · exact h1
      have hy_not_com : y ∉ ⁅twoPoint H t, twoPoint H t⁆ := by
        intro hy
        have hmem : y ∈ B ⊓ P := Subgroup.mem_inf.mpr ⟨hcomB hy, hyP⟩
        rw [hBinf] at hmem
        exact hy1 (Subgroup.mem_bot.mp hmem)
      have hp_com : p ∣ (⁅twoPoint H t, twoPoint H t⁆).relIndex (twoPoint H t) := by
        have hkey := Subgroup.relIndex_mul_relIndex ⁅twoPoint H t, twoPoint H t⁆ B
          (twoPoint H t) hcomB hBleD
        rw [← hkey, hBrel]
        exact dvd_mul_left p _
      have hyE : y ∈ H ⊓ twoPoint H t :=
        Subgroup.mem_inf.mpr ⟨hDleH (hPleD hyP), hPleD hyP⟩
      have hycom : y ∉ ⁅H ⊓ twoPoint H t, H ⊓ twoPoint H t⁆ := by
        rw [inf_eq_right.mpr hDleH] at *
        exact hy_not_com
      have hpcom : p ∣ (⁅H ⊓ twoPoint H t, H ⊓ twoPoint H t⁆).relIndex (H ⊓ twoPoint H t) := by
        rw [inf_eq_right.mpr hDleH] at *
        exact hp_com
      have hyH : y ∉ Work.Grun.pResidual p H :=
        hTrans G (E := H ⊓ twoPoint H t) (W := H) (y := y) hpc hyE hy1
          ⟨1, by rw [pow_one, hyord]⟩ hycom hpcom
      have hyW : y ∈ W := hPleW hyP
      have hyWres : y ∉ Work.Grun.pResidual p W := fun hmem =>
        hyH (pResidual_mono p h.le hmem)
      have hEidx : ¬ p ∣ ((W ⊓ twoPoint H t).subgroupOf W).index := by
        have hkey := Work.LocalPrelim.relIndex_sup_eq_relIndex_inf_auxL (H := twoPoint H t)
          (W := W) (hDleH.trans h.normal)
        have hkey' : (W ⊓ twoPoint H t).relIndex W = (twoPoint H t).relIndex H := by
          rw [inf_comm, ← hkey, sup_comm, h.sup]
        have hnot : ¬ p ∣ (twoPoint H t).relIndex H := by
          have hh := hpc.2.1
          rwa [inf_eq_right.mpr hDleH] at hh
        rwa [show ((W ⊓ twoPoint H t).subgroupOf W).index =
          (W ⊓ twoPoint H t).relIndex W from rfl, hkey']
      obtain ⟨W₁, hW₁lt, hW₁H, hHW₁, hW₁sup⟩ :=
        hStrat G (E := W ⊓ twoPoint H t) (W := W) (D := twoPoint H t) (H := H) (p := p)
          (y := y) inf_le_left inf_le_right hEidx h.le h.normal h.sup hyW hyWres
      obtain ⟨hmWle, hmWnorm, hmWsup, hmWmin⟩ := h.minW
      have hcard := hmWmin W₁ hW₁H hHW₁ hW₁sup
      have hdvd : Nat.card ↥W₁ ∣ Nat.card ↥W := Subgroup.card_dvd_of_le hW₁lt.le
      have hne : Nat.card ↥W₁ ≠ Nat.card ↥W := fun heq =>
        (ne_of_lt hW₁lt) (Subgroup.eq_of_le_of_card_ge hW₁lt.le (le_of_eq heq.symm))
      have hlt : Nat.card ↥W₁ < Nat.card ↥W :=
        lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) hne
      omega
    · -- Case 2: the second alternative of `Section2Prop` is impossible.
      have hP'syl : IsSylowIn p P' (twoPoint H t) := by
        rwa [inf_eq_right.mpr hDleH] at hP'syl₀
      by_cases hcase : P' ⊓ A = ⊥
      · -- `|P'| ≤ p`, so `|P'| = p = |P|` and `P` is a Sylow of `D`.
        have hP'dvd : p ∣ Nat.card ↥P' := by
          rw [← h.P_card]
          exact card_dvd_card_of_isPGroup_of_isSylowIn h.prime hPleD hPp hP'syl
        have hle_p : Nat.card ↥P' ≤ p := by
          have hcard_sup : Nat.card ↥(A ⊔ P') = Nat.card ↥A * Nat.card ↥P' := by
            have hh := card_sup_mul_card_inf (H := A) (K := P') (hP'leV.trans hVnormA)
            rw [inf_comm, hcase, Subgroup.card_bot, mul_one] at hh
            exact hh
          have hleV : A ⊔ P' ≤ centD H t := sup_le hAleV hP'leV
          have hprod : Nat.card ↥A * p = Nat.card ↥(centD H t) := by
            have hh := card_sup_mul_card_inf (H := A) (K := P) (hPleV.trans hVnormA)
            rw [h.A_sup, h.A_inf, Subgroup.card_bot, mul_one, h.P_card] at hh
            exact hh.symm
          have h1 : Nat.card ↥A * Nat.card ↥P' ≤ Nat.card ↥A * p := by
            rw [← hcard_sup, hprod]
            exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hleV)
          exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
        have hP'card : Nat.card ↥P' = p := le_antisymm hle_p (Nat.le_of_dvd Nat.card_pos hP'dvd)
        refine ⟨hPp, hPleD, ?_⟩
        have hPrel : P.relIndex (twoPoint H t) = P'.relIndex (twoPoint H t) := by
          have h1 := relIndex_mul_card_of_le' hPleD
          have h2 := relIndex_mul_card_of_le' hP'syl.2.1
          rw [h.P_card] at h1
          rw [hP'card] at h2
          exact Nat.mul_right_cancel (Nat.pos_of_ne_zero h.prime.ne_zero) (h1.trans h2.symm)
        rw [show (P.subgroupOf (twoPoint H t)).index = P.relIndex (twoPoint H t) from rfl, hPrel]
        exact hP'syl.2.2
      · -- `P' ⊓ A ≠ 1`: an element of `A` acting fixed-point-freely on `K`, absurd.
        exfalso
        have hP'p : IsPGroup p ↥P' := hP'syl.1
        have hP'infp : IsPGroup p ↥(P' ⊓ A) := hP'p.to_le inf_le_left
        have hP'dvd : p ∣ Nat.card ↥(P' ⊓ A) := by
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP'infp
          have hne1 : Nat.card ↥(P' ⊓ A) ≠ 1 := by
            rw [Ne, Subgroup.card_eq_one]
            exact hcase
          have hk0 : k ≠ 0 := by
            intro h0; rw [h0, pow_zero] at hk; exact hne1 hk
          rw [hk]
          exact dvd_pow_self p hk0
        obtain ⟨w, hword⟩ := exists_prime_orderOf_dvd_card' p hP'dvd
        have hwP' : (w : G) ∈ P' := (Subgroup.mem_inf.mp w.2).1
        have hwA : (w : G) ∈ A := (Subgroup.mem_inf.mp w.2).2
        have hword' : orderOf (w : G) = p := by rw [Subgroup.orderOf_coe, hword]
        have hwne : (w : G) ≠ 1 := by
          intro h1; rw [h1, orderOf_one] at hword'; exact h.prime.ne_one hword'.symm
        obtain ⟨k, hkCK, hk1⟩ := hck
        have hkK : k ∈ Work.NormalComplement.Kset (twoPoint H t) t := hkCK.1
        have hkcomm : (w : G) * k * (w : G)⁻¹ = k := by
          have hcomm := (Subgroup.mem_centralizer_iff.mp hkCK.2) (w : G) hwA
          rw [hcomm]; group
        exact hk1 (hP'fpf (w : G) hwP' hwne k hkK hkcomm)
  -- ## the second and third conjuncts: `E = E' ⋊ P`
  have hAN : A ≤ Subgroup.normalizer ((Work.NormalComplement.Kgrp (twoPoint H t) t : Subgroup G) : Set G) :=
    hAleV.trans (hVleD.trans hDnormKg)
  have hBN : B ≤ Subgroup.normalizer ((Work.NormalComplement.Kgrp (twoPoint H t) t : Subgroup G) : Set G) := by
    rw [hB]
    exact sup_le Subgroup.le_normalizer hAN
  have hWiA_le : W ⊓ A ≤ Design.Ecomm H t W := by
    intro x hx
    by_contra hxE'
    obtain ⟨hxW, hxA⟩ := Subgroup.mem_inf.mp hx
    have hxEgrp : x ∈ Design.Egrp H t W := Subgroup.mem_inf.mpr ⟨hxW, hAleD hxA⟩
    have hxV : x ∈ centD H t := hAleV hxA
    obtain ⟨k, hkCK, hk1⟩ := hck
    have hkK : k ∈ Work.NormalComplement.Kset (twoPoint H t) t := hkCK.1
    have hkcomm : x * k * x⁻¹ = k := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp hkCK.2) x hxA
      rw [hcomm]; group
    exact hk1 (hs2_fpf x (Subgroup.mem_inf.mpr ⟨hxEgrp, hxV⟩) hxE' k hkK hkcomm)
  have hM_le_E' : W ⊓ B ≤ Design.Ecomm H t W := by
    intro x hx
    obtain ⟨hxW, hxBg⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hkKg, a, haA, hx'⟩ := NC4.exists_mul_mem_of_sup_eq (E := B) (S := Work.NormalComplement.Kgrp (twoPoint H t) t) (T := A)
      (fun _ hx => Subgroup.mem_sup_left hx) (fun _ hx => Subgroup.mem_sup_right hx) (by rw [hB]) hBN x hxBg
    have haW : a ∈ W := by
      have ha : a = k⁻¹ * x := by rw [hx']; group
      rw [ha]
      exact W.mul_mem (W.inv_mem (hKgW hkKg)) hxW
    rw [hx']
    exact (Design.Ecomm H t W).mul_mem (hKg_le hkKg)
      (hWiA_le (Subgroup.mem_inf.mpr ⟨haW, haA⟩))
  have hE'_eq_M : Design.Ecomm H t W = W ⊓ B := by
    refine le_antisymm ?_ hM_le_E'
    rw [Design.Ecomm, hEq]
    refine commutator_le_of_sup_eq_of_comm (B := W ⊓ B) (P := P) (E := (W ⊓ B) ⊔ P)
      ?_ hPcomm rfl
    rw [← hEq]
    refine Subgroup.le_normalizer_iff.mpr ?_
    intro x hx m hm
    obtain ⟨hxW, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hmW, hmB⟩ := Subgroup.mem_inf.mp hm
    exact Subgroup.mem_inf.mpr ⟨W.mul_mem (W.mul_mem hxW hmW) (W.inv_mem hxW),
      (Subgroup.mem_normalizer_iff.mp (hBnorm hxD) m).mp hmB⟩
  refine ⟨hPsyl, ?_, ?_⟩
  · rw [hE'_eq_M, inf_assoc, hBinf, inf_bot_eq]
  · rw [hE'_eq_M, ← hEq]

end Work.NormalComplement.S5K
