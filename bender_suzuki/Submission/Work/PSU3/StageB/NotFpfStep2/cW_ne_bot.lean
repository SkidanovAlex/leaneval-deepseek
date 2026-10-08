/-
# `Work.PSU3.StageB.NotFpfStep2.cW_ne_bot`

Peterfalvi II, Ch. VII §4 (2) (pp. 278–280): if `P` is a prime-order subgroup of `V = C_D(t)`
centralising some element of `Q ∖ Q₀`, then `C_W(P) ≠ 1`: there is `ζ ∈ W#` with `P` centralising
`ζ`.

## Strategy

* `W = C_D(Inv H)` is normal in `D` (Ch. II §4 Prop. 4), so `P ≤ V ≤ D` acts on `W`; and
  `P ⊓ W = 1` because `W#` acts fixed-point-freely on `Q ∖ Q₀` (`W_semireg`, Ch. VI §1 case c).
* Ch. V §2 Lemma 2 c) (`lemma2cHig`) gives, for `X = P`, the local trichotomy.  The case
  `orderOf (s*t) = 5` is excluded because the ambient situation is case c) of Ch. VI §1, i.e.
  `orderOf (s*t) = 3` (obtained from `lemma2cHig` applied to a prime-order subgroup of `W`,
  which pins down `C_Q(P') = Q0sub H`), and the case `|C_Q(P)| = |C_{Q₀}(P)|` is excluded by the
  given point `y ∈ Q ∖ Q₀` fixed by `P`.  So the third alternative holds: there is
  `x ∈ D ⊓ C_G(P)` with `x ∉ P` centralising `C_{Q₀}(P) = Q0sub H ⊓ C_G(P)`.
* The action of `K` on `Q₀ ≅ F` is by multiplication (Ch. V §1 Prop. 3), that of `V/W` by field
  automorphisms.  Since `x` fixes `C_{Q₀}(P)`, and the field element `1 ∈ Fix(ρ P)` corresponds to
  an element of `Q0sub H` centralised by `P`, the `K`-component of `x` is trivial: `x ∈ V`.
* Galois theory (Artin) then gives `x ∈ P · W`; writing `x = p w` with `p ∈ P`, `w ∈ W`, the
  element `w = p⁻¹ x` is a nontrivial element of `C_W(P)`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageA.lemma2c
import Submission.Work.PSU3.StageA.lemma2cHig
import Submission.Work.PSU3.StageA.caseC_frame_core
import Submission.Work.PSU3.StageA.caseC_st_structure
import Submission.Work.PSU3.StageA.twoPoint_eq_Kset_mul_centD
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.GaloisField.fixedField_card
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV12.mem_fixedField_iff_mem_centralizer
import Submission.Work.ThmF.ChV12.card_map_subgroupOf_eq
import Submission.Work.ThmF.ChV12.fixedField_card_pow
import Submission.Work.ThmF.ChV12.KsubSubgroupOfNormal
import Submission.Work.ThmF.ChV12.L5Base

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.PSU3.StageB.NotFpfStep2

open Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `W = C_V(Kset) = D ⊓ C_G(Inv H)` (Peterfalvi II, Ch. II §4 Prop. 4). -/
theorem W_eq_twoPoint_inter_centralizer (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    W H t = twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) :=
  (hC4 G hS.situation H hS.split.stronglyEmbedded t hS.split.invol hS.split.not_mem).2.2.2.2.1

/-- `W ≠ 1` for a coarse frame: `fr.ζ` is a nontrivial element of `W`. -/
theorem W_ne_bot_of_frame (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : W H t ≠ ⊥ := by
  intro h
  have h1 : ((fr.ζ : fr.KW) : G) ∈ (⊥ : Subgroup G) := by
    rw [← h]; exact fr.ζ_mem_W
  exact fr.ζ_ne_one (Subtype.coe_injective (Subgroup.mem_bot.mp h1))

/-- If `P` centralises a point `y ∈ Q ∖ Q₀`, then `P ⊓ W = ⊥`. -/
theorem inf_W_eq_bot_of_centralizes (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) {P : Subgroup G} {y : G}
    (hyQ : y ∈ Q) (hy0 : y ∉ fr.Q0) (hyc : ∀ p ∈ P, p * y = y * p) :
    P ⊓ W H t = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro p hp
  rw [Subgroup.mem_inf] at hp
  rw [Subgroup.mem_bot]
  by_contra hp1
  exact hy0 (fr.W_semireg p hp.2 hp1 y hyQ (hyc p hp.1))

/-- A nontrivial subgroup of a finite group has a prime-order subgroup. -/
theorem exists_prime_subgroup_le {X : Subgroup G} (hX : X ≠ ⊥) :
    ∃ P : Subgroup G, P ≤ X ∧ (Nat.card P).Prime := by
  have hx : ∃ x : ↥X, x ≠ 1 := by
    by_contra h
    refine hX (le_antisymm (fun x hxm => Subgroup.mem_bot.mpr ?_) bot_le)
    by_contra hx1
    exact h ⟨⟨x, hxm⟩, fun hxx => hx1 (Subtype.ext_iff.mp hxx)⟩
  obtain ⟨x0, hx0⟩ := hx
  haveI : Fintype ↥X := Fintype.ofFinite _
  have hcard : Nat.card ↥X ≠ 1 := by
    have hlt : 1 < Nat.card ↥X := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card_iff.mpr ⟨x0, 1, hx0⟩
    omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  refine ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.mpr x.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  exact hp

/-- Every two elements of a prime-order subgroup commute. -/
theorem comm_of_prime_card {P : Subgroup G} (hP : (Nat.card P).Prime) :
    ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro a ha b hb
  rcases eq_or_ne a 1 with rfl | ha1
  · rw [one_mul, mul_one]
  rcases eq_or_ne b 1 with rfl | hb1
  · rw [mul_one, one_mul]
  have ha_dvd : orderOf a ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P ha
  have ha_eq : orderOf a = Nat.card P := by
    rcases (Nat.dvd_prime hP).mp ha_dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hb_mem : b ∈ Subgroup.zpowers a := by
    have hle : Subgroup.zpowers a ≤ P := Subgroup.zpowers_le.mpr ha
    have hcard_eq : Nat.card ↥(Subgroup.zpowers a) = Nat.card P := by
      rw [Nat.card_zpowers, ha_eq]
    have hEq := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard_eq.symm)
    rw [hEq]; exact hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb_mem
  rw [← hk]
  exact (Commute.refl a).zpow_right k |>.eq

/-- **The ambient situation is case c) of Ch. VI §1**: `orderOf (s * t) = 3`.

Apply Ch. V §2 Lemma 2 c) (`lemma2cHig`) to a prime-order subgroup `P'` of `W`.  The
semiregularity of `W#` gives `C_Q(P') = Q0sub H`, and `Q0sub H ≤ C(P')` (case c), so the three
alternatives read `|C_{Q₀}(P')| = |Q0sub H|`, resp. `|Q0sub H|²`, resp. `|Q0sub H|³`; the last two
are impossible because `s ∈ Q0sub H ∖ {1}`. -/
theorem orderOf_st_eq_three (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) {s r : G}
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r) :
    orderOf (s * t) = 3 := by
  classical
  have hWne : W H t ≠ ⊥ := W_ne_bot_of_frame hS fr
  obtain ⟨P', hP'W, hP'p⟩ := exists_prime_subgroup_le hWne
  have hP'V : P' ≤ centD H t := hP'W.trans (W_le_centD H t)
  have htri := Work.PSU3.StageA.lemma2cHig hS hC4 Work.PSU3.benderSTProp hs hs2 hr hsr hP'V hP'p
  -- `P' ≤ W ≤ D ⊓ C(Inv H)` centralises `Q0sub H`
  have hQ0sub_le_C : Work.ThmF.Q0sub H ≤ Subgroup.centralizer (P' : Set G) := by
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr (fun p hp => ?_)
    have hmem : p ∈ twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) :=
      (W_eq_twoPoint_inter_centralizer hS hC4) ▸ hP'W hp
    have hcent : p ∈ Subgroup.centralizer (involutions (H : Set G)) := (Subgroup.mem_inf.mp hmem).2
    have hQ : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({p} : Set G) := by
      rw [Work.ThmF.Q0sub]
      refine (Subgroup.closure_le _).mpr ?_
      intro u hu
      rw [Work.ThmF.mem_Q0_iff] at hu
      rcases hu with ⟨huH, hu2⟩ | rfl
      · exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
          rw [Set.mem_singleton_iff] at hw; subst hw
          exact (Subgroup.mem_centralizer_iff.mp hcent u ⟨huH, hu2⟩).symm)
      · exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
          rw [Set.mem_singleton_iff] at hw; subst hw; rw [one_mul, mul_one])
    exact Subgroup.mem_centralizer_iff.mp (hQ hz) p (Set.mem_singleton p)
  -- `s ∈ Q0sub H` is nontrivial, so `|Q0sub H| ≥ 2`
  have hsQ0sub : s ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Or.inl ⟨hS.split.le hs, hs2⟩)
  have hQ0card : 2 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    haveI : Fintype ↥(Work.ThmF.Q0sub H) := Fintype.ofFinite _
    have h1 : 1 < Nat.card ↥(Work.ThmF.Q0sub H) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card_iff.mpr ⟨⟨s, hsQ0sub⟩, 1, fun h => by
        have h2 : s = (1 : G) := Subtype.ext_iff.mp h
        rw [h2] at hs2
        exact absurd hs2 (by simp)⟩
    omega
  -- `C_Q(P') = Q0sub H` and `|C_{Q₀}(P')| = |Q0sub H|`
  have hCeq : Q ⊓ Subgroup.centralizer (P' : Set G) = Work.ThmF.Q0sub H := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzQ, hzc⟩ := Subgroup.mem_inf.mp hz
      have hP'ne : P' ≠ ⊥ := by
        intro h; rw [h, Subgroup.card_bot] at hP'p; exact Nat.not_prime_one hP'p
      obtain ⟨p, hpP', hp1⟩ : ∃ p ∈ P', p ≠ 1 := by
        by_contra h
        push_neg at h
        exact hP'ne (le_antisymm (fun x hx => Subgroup.mem_bot.mpr (h x hx)) bot_le)
      have hcomm : p * z = z * p := Subgroup.mem_centralizer_iff.mp hzc p hpP'
      have hz' := fr.W_semireg p (hP'W hpP') hp1 z hzQ hcomm
      rwa [Work.PSU3.StageB.frameQ0_eq_Q0sub hS fr] at hz'
    · intro z hz
      exact ⟨Work.PSU3.StageA.Q0sub_le_Q hS.split hz, hQ0sub_le_C hz⟩
  have hℓeq : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P' : Set G)) =
      Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [inf_eq_left.mpr hQ0sub_le_C]
  rcases htri with ⟨h1, -, -⟩ | ⟨h1, -, h3, -⟩ | ⟨h1, -, -⟩
  · exact h1
  · exfalso
    rw [hCeq, hℓeq] at h3
    have h2 : (1 : ℕ) = Nat.card ↥(Work.ThmF.Q0sub H) := by
      have h3' : Nat.card ↥(Work.ThmF.Q0sub H) * 1 =
          Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H) := by
        rw [mul_one, ← pow_two, ← h3]
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3'
    omega
  · exact h1

theorem cW_ne_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hnfpf : ¬ Work.PSU3.DFpfBar H Q t) {P : Subgroup G}
    (hPV : P ≤ Submission.Blueprint.centD H t) (hPprime : (Nat.card P).Prime)
    (hPy : ∃ y ∈ Q, y ∉ fr.Q0 ∧ ∀ p ∈ P, p⁻¹ * y * p = y) :
    ∃ ζ : G, ζ ∈ Work.ThmF.W H t ∧ ζ ≠ 1 ∧ ∀ p ∈ P, p⁻¹ * ζ * p = ζ := by
  classical
  obtain ⟨y, hyQ, hy0fr, hycent⟩ := hPy
  have hy0 : y ∉ Work.ThmF.Q0sub H := by
    rw [← Work.PSU3.StageB.frameQ0_eq_Q0sub hS fr]; exact hy0fr
  have hycent' : ∀ p ∈ P, p * y = y * p := by
    intro p hp
    have h := hycent p hp
    calc p * y = p * (p⁻¹ * y * p) := by rw [h]
      _ = y * p := by group
  have hWne : W H t ≠ ⊥ := W_ne_bot_of_frame hS fr
  have hPW : P ⊓ W H t = ⊥ := inf_W_eq_bot_of_centralizes hS fr hyQ hy0fr hycent'
  obtain ⟨s, hsQ, hs2, r, hrQ, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hst3 : orderOf (s * t) = 3 := orderOf_st_eq_three hS hC4 fr hsQ hs2 hrQ hsr
  -- ### extract the element `x ∈ D ⊓ C(P) ∖ P` centralising `C_{Q₀}(P)`
  have hx_exists : ∃ x ∈ twoPoint H t ⊓ Subgroup.centralizer (P : Set G), x ∉ P ∧
      ∀ z ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G), x * z = z * x := by
    have htri := Work.PSU3.StageA.lemma2cHig hS hC4 Work.PSU3.benderSTProp hsQ hs2 hrQ hsr hPV hPprime
    rcases htri with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · exfalso
      have hle : Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) ≤
          Q ⊓ Subgroup.centralizer (P : Set G) :=
        inf_le_inf (Work.PSU3.StageA.Q0sub_le_Q hS.split) le_rfl
      have heq : Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) =
          Q ⊓ Subgroup.centralizer (P : Set G) :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq h3)
      have hyA : y ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) := by
        rw [heq]
        exact ⟨hyQ, Subgroup.mem_centralizer_iff.mpr (fun p hp => hycent' p hp)⟩
      exact hy0 hyA.1
    · exfalso
      exact absurd (h1.symm.trans hst3) (by norm_num : (5 : ℕ) ≠ 3)
    · exact h3
  obtain ⟨x, hxD, hxnotP, hxfix0⟩ := hx_exists
  have hxC : x ∈ Subgroup.centralizer (P : Set G) := hxD.2
  have hxfixC : ∀ z ∈ Work.ThmF.Q0sub H, (z : G) ∈ Subgroup.centralizer (P : Set G) →
      x * z = z * x := fun z hz hzc => hxfix0 z (Subgroup.mem_inf.mpr ⟨hz, hzc⟩)
  -- ### the field data of Ch. V §1 Prop. 3
  have hKsub : (Ksub H t : Set G) = Kset H t := (Work.PSU3.StageA.caseC_Ksub_cyc hS hC4 hWne).1
  have hKcyc : IsCyclic ↥(Ksub H t) := (Work.PSU3.StageA.caseC_Ksub_cyc hS hC4 hWne).2
  have hKn : ((Ksub H t).subgroupOf (twoPoint H t)).Normal :=
    Work.ThmF.ChV12.KsubSubgroupOfNormal hS.split hKsub
  have hcomm := Work.PSU3.StageA.caseC_involutions_comm hS hC4
  have hreg := Work.ThmF.L5.Kset_regular hS.split
  have hVeq : centD H t = twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    Work.PSU3.StageA.centD_eq_centralizer_s hS hsQ hs2 hrQ hsr
  have hsInv : s ∈ involutions (H : Set G) := ⟨hS.split.le hsQ, hs2⟩
  obtain ⟨F, hFld, hFint, e, κ, ρ, hcardF, hactK, hactV, hker⟩ :=
    Work.ThmF.ChV12.prop3 H Q t hS.split hcomm hKsub hKcyc hKn hreg s hsInv hVeq
  letI : Field F := hFld
  letI : Fintype F := hFint
  let A : Subgroup (F ≃+* F) := Subgroup.map ρ (P.subgroupOf (centD H t))
  have hconjQ0 : ∀ v ∈ H, ∀ z ∈ Work.ThmF.Q0sub H, v * z * v⁻¹ ∈ Work.ThmF.Q0sub H :=
    fun v hv z hz => Work.ThmF.ChV12.conj_mem_Q0sub hv hz
  have hkey : ∀ z : ↥(Work.ThmF.Q0sub H),
      Multiplicative.toAdd (e z) ∈ FixedPoints.subfield A F ↔
        (z : G) ∈ Subgroup.centralizer (P : Set G) :=
    fun z => Work.ThmF.ChV12.mem_fixedField_iff_mem_centralizer H Q t hPV hconjQ0 e ρ hactV z
  -- ### Galois step: elements of `V` fixing `C_{Q₀}(P)` lie in `P · W`
  have galois : ∀ v ∈ centD H t,
      (∀ z ∈ Work.ThmF.Q0sub H, (z : G) ∈ Subgroup.centralizer (P : Set G) → v * z = z * v) →
      v ∈ (P : Set G) * (W H t : Set G) := by
    intro v hvV hfixv
    let vV : ↥(centD H t) := ⟨v, hvV⟩
    have hrhoA : ∀ y ∈ FixedPoints.subfield A F, ρ vV y = y := by
      intro y hy
      let z : ↥(Work.ThmF.Q0sub H) := e.symm (Multiplicative.ofAdd y)
      have hzy : Multiplicative.toAdd (e z) = y := by
        show Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd y))) = y
        rw [MulEquiv.apply_symm_apply]; rfl
      have hzc : (z : G) ∈ Subgroup.centralizer (P : Set G) := (hkey z).mp (by rw [hzy]; exact hy)
      have hcommvz : v * (z : G) = (z : G) * v := hfixv z z.2 hzc
      have hconj : v * (z : G) * v⁻¹ = (z : G) := by rw [hcommvz]; group
      have hvH : v ∈ H := (Work.ThmF.centD_le_twoPoint t hvV).1
      have hzmem : v * (z : G) * v⁻¹ ∈ Work.ThmF.Q0sub H := hconjQ0 v hvH (z : G) z.2
      have h1 : Multiplicative.toAdd (e ⟨v * (z : G) * v⁻¹, hzmem⟩) =
          ρ vV (Multiplicative.toAdd (e z)) := hactV vV z hzmem
      have h2 : (⟨v * (z : G) * v⁻¹, hzmem⟩ : ↥(Work.ThmF.Q0sub H)) = z := Subtype.ext hconj
      show ρ vV y = y
      rw [← hzy, ← h1, h2, hzy]
    let B : Subgroup (F ≃+* F) := A ⊔ Subgroup.zpowers (ρ vV)
    have hmemOf : ∀ (C : Subgroup (F ≃+* F)) {y : F},
        y ∈ FixedPoints.subfield C F ↔ ∀ σ ∈ C, σ y = y := by
      intro C y
      constructor
      · intro h σ hσ
        simpa using h ⟨σ, hσ⟩
      · intro h m
        show (m : F ≃+* F) y = y
        exact h (m : F ≃+* F) m.2
    have hfixAB : FixedPoints.subfield A F = FixedPoints.subfield B F := by
      refine le_antisymm ?_ ?_
      · intro y hy
        have hyA : ∀ σ ∈ A, σ y = y := (hmemOf A).mp hy
        have hstab : B ≤ MulAction.stabilizer (F ≃+* F) y := by
          refine sup_le ?_ ?_
          · intro σ hσ; exact MulAction.mem_stabilizer_iff.mpr (hyA σ hσ)
          · refine Subgroup.zpowers_le.mpr ?_
            exact MulAction.mem_stabilizer_iff.mpr (hrhoA y hy)
        rw [hmemOf B]
        intro σ hσ
        exact MulAction.mem_stabilizer_iff.mp (hstab hσ)
      · intro y hy
        rw [hmemOf A]
        intro σ hσ
        exact (hmemOf B).mp hy σ (Subgroup.mem_sup_left hσ)
    haveI : Fintype (F ≃+* F) :=
      Fintype.ofInjective (fun f : F ≃+* F => (f : F → F))
        (fun f g h => RingEquiv.ext (congrFun h))
    have hcardA := Work.ThmF.ChV12.fixedField_card_pow (F := F) A
    have hcardB := Work.ThmF.ChV12.fixedField_card_pow (F := F) B
    have h2le : 2 ≤ Nat.card ↥(FixedPoints.subfield A F) := by
      have h01 : (0 : FixedPoints.subfield A F) ≠ 1 := by
        intro h; exact zero_ne_one (congrArg Subtype.val h)
      have hlt : 1 < Fintype.card ↥(FixedPoints.subfield A F) :=
        Fintype.one_lt_card_iff.mpr ⟨0, 1, h01⟩
      rw [Nat.card_eq_fintype_card]
      omega
    have hcardFB : Nat.card ↥(FixedPoints.subfield B F) =
        Nat.card ↥(FixedPoints.subfield A F) := by rw [hfixAB]
    have hABcard : Nat.card A = Nat.card B := by
      refine Nat.pow_right_injective h2le ?_
      show Nat.card ↥(FixedPoints.subfield A F) ^ Nat.card A =
        Nat.card ↥(FixedPoints.subfield A F) ^ Nat.card B
      rw [hcardA, ← hcardB, hcardFB]
    have hAB : A = B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [← hABcard])
    have hmem : ρ vV ∈ A := by
      rw [hAB]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (ρ vV))
    obtain ⟨p₀, hp₀mem, hp₀eq⟩ := Subgroup.mem_map.mp hmem
    have hp₀P : ((p₀ : ↥(centD H t)) : G) ∈ P := Subgroup.mem_subgroupOf.mp hp₀mem
    have hWmem : ((p₀ : ↥(centD H t)) : G)⁻¹ * v ∈ W H t := by
      have h1 : (p₀⁻¹ * vV : ↥(centD H t)) ∈ (W H t).subgroupOf (centD H t) := by
        rw [← hker, MonoidHom.mem_ker]
        show ρ (p₀⁻¹ * vV) = 1
        rw [map_mul, map_inv, hp₀eq, inv_mul_cancel]
      simpa using Subgroup.mem_subgroupOf.mp h1
    rw [Set.mem_mul]
    exact ⟨((p₀ : ↥(centD H t)) : G), hp₀P, ((p₀ : ↥(centD H t)) : G)⁻¹ * v, hWmem, by group⟩
  -- ### the `K`-component of `x` is trivial
  obtain ⟨k, hkKset, v, hvV, hxkv⟩ := Work.PSU3.StageA.twoPoint_eq_Kset_mul_centD hS.split x hxD.1
  have hkH : k ∈ H := (Subgroup.mem_inf.mp (Work.ThmF.Kset_subset H t hkKset)).1
  have hkKsub : k ∈ Ksub H t := Work.ThmF.Kset_le_Ksub H t hkKset
  have hvH : v ∈ H := (Work.ThmF.centD_le_twoPoint t hvV).1
  let z₀ : ↥(Work.ThmF.Q0sub H) := e.symm (Multiplicative.ofAdd (1 : F))
  have hz₀_toAdd : Multiplicative.toAdd (e z₀) = 1 := by
    show Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd (1 : F)))) = 1
    rw [MulEquiv.apply_symm_apply]; rfl
  have hz₀_cent : (z₀ : G) ∈ Subgroup.centralizer (P : Set G) :=
    (hkey z₀).mp (by rw [hz₀_toAdd]; exact one_mem _)
  have hxz₀ : x * (z₀ : G) = (z₀ : G) * x := hxfixC z₀ z₀.2 hz₀_cent
  -- step 1: conjugate by `v`
  have hw1_mem : v * (z₀ : G) * v⁻¹ ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.ChV12.conj_mem_Q0sub hvH z₀.2
  have hw1_toAdd : Multiplicative.toAdd (e ⟨v * (z₀ : G) * v⁻¹, hw1_mem⟩) = 1 := by
    have h := hactV (⟨v, hvV⟩ : ↥(centD H t)) z₀ hw1_mem
    rw [hz₀_toAdd, map_one] at h
    exact h
  -- step 2: conjugate by `k`
  have hw2_mem : k * (v * (z₀ : G) * v⁻¹) * k⁻¹ ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.ChV12.conj_mem_Q0sub hkH hw1_mem
  have hw2_toAdd : Multiplicative.toAdd (e ⟨k * (v * (z₀ : G) * v⁻¹) * k⁻¹, hw2_mem⟩) =
      ((κ (⟨k, hkKsub⟩ : ↥(Ksub H t))) : F) := by
    have h := hactK (⟨k, hkKsub⟩ : ↥(Ksub H t))
      (⟨v * (z₀ : G) * v⁻¹, hw1_mem⟩ : ↥(Work.ThmF.Q0sub H)) hw2_mem
    rw [hw1_toAdd, mul_one] at h
    exact h
  have hw2_eq : k * (v * (z₀ : G) * v⁻¹) * k⁻¹ = (z₀ : G) := by
    have hA : k * (v * (z₀ : G) * v⁻¹) * k⁻¹ = k * v * (z₀ : G) * (k * v)⁻¹ := by group
    have h : k * v * (z₀ : G) * (k * v)⁻¹ = (z₀ : G) := by
      have h0 : x * (z₀ : G) * x⁻¹ = (z₀ : G) := by rw [hxz₀]; group
      rwa [hxkv] at h0
    exact hA.trans h
  have hκeq : ((κ (⟨k, hkKsub⟩ : ↥(Ksub H t))) : F) = 1 := by
    have hz : (⟨k * (v * (z₀ : G) * v⁻¹) * k⁻¹, hw2_mem⟩ : ↥(Work.ThmF.Q0sub H)) = z₀ :=
      Subtype.ext hw2_eq
    have h : Multiplicative.toAdd (e ⟨k * (v * (z₀ : G) * v⁻¹) * k⁻¹, hw2_mem⟩) = 1 := by
      rw [hz, hz₀_toAdd]
    rw [hw2_toAdd] at h
    exact h
  have hk1 : k = 1 := by
    have hv : κ (⟨k, hkKsub⟩ : ↥(Ksub H t)) = 1 := Units.val_eq_one.mp hκeq
    have h : (⟨k, hkKsub⟩ : ↥(Ksub H t)) = 1 := κ.injective (by rw [hv, map_one])
    exact congrArg (fun z : ↥(Ksub H t) => (z : G)) h
  have hxV : x ∈ centD H t := by
    rw [hxkv, hk1, one_mul]; exact hvV
  -- ### conclude
  have hxPW : x ∈ (P : Set G) * (W H t : Set G) := galois x hxV hxfixC
  rw [Set.mem_mul] at hxPW
  obtain ⟨p₀, hp₀P, w, hwW, hp₀w⟩ := hxPW
  refine ⟨w, hwW, ?_, ?_⟩
  · intro hw1
    refine hxnotP ?_
    rw [← hp₀w, hw1, mul_one]; exact hp₀P
  · intro p hp
    have hw_eq : w = p₀⁻¹ * x := by rw [← hp₀w]; group
    have hPcomm := comm_of_prime_card hPprime
    have hxconj : p⁻¹ * x * p = x := by
      have h := Subgroup.mem_centralizer_iff.mp hxC p hp
      calc p⁻¹ * x * p = p⁻¹ * (x * p) := by group
        _ = p⁻¹ * (p * x) := by rw [← h]
        _ = x := by group
    have hcomm : p⁻¹ * p₀⁻¹ = p₀⁻¹ * p⁻¹ :=
      hPcomm p⁻¹ (P.inv_mem hp) p₀⁻¹ (P.inv_mem hp₀P)
    rw [hw_eq]
    calc p⁻¹ * (p₀⁻¹ * x) * p = (p⁻¹ * p₀⁻¹) * x * p := by group
      _ = (p₀⁻¹ * p⁻¹) * x * p := by rw [hcomm]
      _ = p₀⁻¹ * (p⁻¹ * x * p) := by group
      _ = p₀⁻¹ * x := by rw [hxconj]

end Work.PSU3.StageB.NotFpfStep2

