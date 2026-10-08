import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.SemiregVendored
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV12.mem_fixedField_iff_mem_centralizer
import Submission.Work.ThmF.ChV12.fixedField_card_pow
import Submission.Work.ThmF.ChV12.card_map_subgroupOf_eq
import Submission.Work.ThmF.ChV12.KsubSubgroupOfNormal
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.caseC_Q0_facts
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.PSU3.StageB.NotFpfStep2

/-!
# `Z(U) ⊆ P` for `U = O^{2'}(C_G(P))` (Peterfalvi II.7.4(1), p. 278)

Source: "As `Z(U) ⊆ C_V(C_{Q₀}(P))`, `Z(U) ⊆ PW` by Galois theory.  Since `P·Z(U)` centralises
`C_Q(P) ⊄ Q₀`, `P·Z(U) ∩ W = 1`, so `Z(U) ⊆ P`."

Compared with the sibling module `Submission.Work.PSU3.StageB.centralizerOddResidual_center_le_P`,
the target here takes `W H t ≠ ⊥` as a *hypothesis* rather than deriving it from the rank-one black
box `Work.PSU3.StageA.rankOneVNeqWProp_proof` (which is a `hole` at the time of writing, so the
sibling module cannot be used as a source of a hole-free proof).  The three helper lemmas below are
copied verbatim from that sibling module (namespace adjusted) so that this file is self-contained.
-/

/-! ## §1. Elementary: `C_Q(P) ≤ O^{2'}(C_G(P))` -/

/-- `Q₀ = Q0sub H` is contained in `Q`. -/
theorem Q0sub_le_Q_of_hyp {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) : Work.ThmF.Q0sub H ≤ Q := by
  refine (Subgroup.closure_le Q).mpr ?_
  intro x hx
  rcases (Work.ThmF.mem_Q0_iff).mp hx with ⟨hxH, hx2⟩ | rfl
  · exact Work.PSU3.StageA.caseC_involutions_subset_Q hS.split ⟨hxH, hx2⟩
  · exact Q.one_mem

/-- Every `2`-element of `C_G(P)` lies in `U = O^{2'}(C_G(P))`; in particular `C_Q(P) ≤ U`
(`Q` is a `2`-group). -/
theorem mem_centralizerOddResidual_of_mem_Q {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (hS : Work.PSU3.PSU3Hyp H Q t) {P : Subgroup G} {x : G}
    (hxQ : x ∈ Q) (hxC : x ∈ Subgroup.centralizer (P : Set G)) :
    x ∈ Work.PSU3.StageB.centralizerOddResidual P := by
  classical
  -- `|Q| = 2 ^ n`, so `x ^ 2 ^ n = 1`
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS.two
  have hx2G : x ^ 2 ^ n = 1 := by
    have hdvd : orderOf x ∣ 2 ^ n := by
      rw [← hn]; exact Subgroup.orderOf_dvd_natCard Q hxQ
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hx2 : (⟨x, hxC⟩ : ↥(Subgroup.centralizer (P : Set G))) ^ 2 ^ n = 1 := by
    apply Subtype.ext
    simpa using hx2G
  -- hence `⟨x, hxC⟩ ∈ O^{2'}(C_G(P))`
  have hxmem : (⟨x, hxC⟩ : ↥(Subgroup.centralizer (P : Set G))) ∈
      Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (P : Set G)) :=
    Work.PSU3.StageA.mem_oddResidual_of_pow_two_eq_one hx2
  exact Subgroup.mem_map_of_mem _ hxmem

/-! ## §2. The Galois step -/

/-- **The Galois step.**  Ch. V §1 Prop. 3 identifies `Q₀` with the additive group of a finite
field `F` on which `V = C_D(t)` acts by field automorphisms with kernel `W`.  Consequently an
element `v ∈ V` which fixes `C_{Q₀}(P) = Q0sub H ⊓ C_G(P)` pointwise fixes the fixed field of
the image `A` of `P` in `Gal(F)`; as `P ⊓ W = 1` the group `P` covers `A`, so `v ∈ P · W`. -/
theorem mem_mul_of_fixes_centralizer_Q0 {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t)
    (hPW : P ⊓ Work.ThmF.W H t = ⊥) (hW : Work.ThmF.W H t ≠ ⊥) :
    ∀ v ∈ Submission.Blueprint.centD H t,
      (∀ x ∈ Work.ThmF.Q0sub H, x ∈ Subgroup.centralizer (P : Set G) → v * x = x * v) →
      v ∈ (P : Set G) * (Work.ThmF.W H t : Set G) := by
  classical
  intro v hvV hfixv
  -- ## structure identity data (`s`, `r`) and the identification `V = D ⊓ C_G(s)`
  obtain ⟨s, hsQ, hs2, r, hrQ, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hV : Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    Work.PSU3.StageA.centD_eq_centralizer_s hS hsQ hs2 hrQ hsr
  -- ## Ch. V §1 Prop. 3
  obtain ⟨hKsub, hKcyc⟩ := Work.PSU3.StageA.Ksub_eq_Kset_of_W_ne_bot hS hC4 hW
  have hKn : ((Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal :=
    Work.ThmF.ChV12.KsubSubgroupOfNormal hS.split hKsub
  have hcomm := Work.PSU3.StageA.caseC_involutions_comm hS hC4
  have hreg := Work.ThmF.L5.Kset_regular hS.split
  have hsInv : s ∈ involutions (H : Set G) := ⟨hS.split.le hsQ, hs2⟩
  obtain ⟨F, hFld, hFint, e, κ, ρ, hcardF, hactK, hactV, hker⟩ :=
    Work.ThmF.ChV12.prop3 H Q t hS.split hcomm hKsub hKcyc hKn hreg s hsInv hV
  letI : Field F := hFld
  letI : Fintype F := hFint
  -- a name for `v` as an element of `V`
  let vV : ↥(Submission.Blueprint.centD H t) := ⟨v, hvV⟩
  -- ## the image `A` of `P` in the automorphism group of `F`
  let A : Subgroup (F ≃+* F) :=
    Subgroup.map ρ (P.subgroupOf (Submission.Blueprint.centD H t))
  have hAcard : Nat.card A = Nat.card P :=
    Work.ThmF.ChV12.card_map_subgroupOf_eq H t P hPV hPW ρ hker
  -- ## the fixed field of `A` is the image of `C_{Q₀}(P)`
  have hkey : ∀ x : ↥(Work.ThmF.Q0sub H),
      Multiplicative.toAdd (e x) ∈ FixedPoints.subfield A F ↔
        (x : G) ∈ Subgroup.centralizer (P : Set G) :=
    fun x => Work.ThmF.ChV12.mem_fixedField_iff_mem_centralizer H Q t hPV
      (fun w hw y hy => Work.ThmF.ChV12.conj_mem_Q0sub hw hy) e ρ hactV x
  -- ## membership in a fixed field of a subgroup, in `σ`-form
  have hmemOf : ∀ (C : Subgroup (F ≃+* F)) {y : F},
      y ∈ FixedPoints.subfield C F ↔ ∀ σ ∈ C, σ y = y := by
    intro C y
    constructor
    · intro h σ hσ
      simpa using h ⟨σ, hσ⟩
    · intro h m
      show (m : F ≃+* F) y = y
      exact h (m : F ≃+* F) m.2
  -- ## `ρ v` fixes the fixed field of `A` pointwise
  have hrhoA : ∀ y ∈ FixedPoints.subfield A F, ρ vV y = y := by
    intro y hy
    -- write `y = toAdd (e x)` for some `x ∈ Q0sub H`
    let x : ↥(Work.ThmF.Q0sub H) := e.symm (Multiplicative.ofAdd y)
    have hex : e x = Multiplicative.ofAdd y := MulEquiv.apply_symm_apply e _
    have hxy : Multiplicative.toAdd (e x) = y := by rw [hex]; rfl
    have hxcent : (x : G) ∈ Subgroup.centralizer (P : Set G) :=
      (hkey x).mp (by rw [hxy]; exact hy)
    -- `v` commutes with `x`
    have hcommvx : v * (x : G) = (x : G) * v := hfixv x x.2 hxcent
    have hconj : v * (x : G) * v⁻¹ = (x : G) := by rw [hcommvx]; group
    have hvH : v ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hvV).1).1
    have hxmem : v * (x : G) * v⁻¹ ∈ Work.ThmF.Q0sub H :=
      Work.ThmF.ChV12.conj_mem_Q0sub hvH x.2
    have h1 : Multiplicative.toAdd (e ⟨v * (x : G) * v⁻¹, hxmem⟩) =
        ρ vV (Multiplicative.toAdd (e x)) := hactV vV x hxmem
    have h2 : (⟨v * (x : G) * v⁻¹, hxmem⟩ : ↥(Work.ThmF.Q0sub H)) = x :=
      Subtype.ext hconj
    show ρ vV y = y
    rw [← hxy, ← h1, h2, hxy]
  -- ## the fixed field of `A ⊔ ⟨ρ v⟩` is the same
  let B : Subgroup (F ≃+* F) := A ⊔ Subgroup.zpowers (ρ vV)
  have hfixAB : FixedPoints.subfield A F = FixedPoints.subfield B F := by
    refine le_antisymm ?_ ?_
    · intro y hy
      have hyA : ∀ σ ∈ A, σ y = y := (hmemOf A).mp hy
      have hstab : B ≤ MulAction.stabilizer (F ≃+* F) y := by
        refine sup_le ?_ ?_
        · intro σ hσ
          exact MulAction.mem_stabilizer_iff.mpr (hyA σ hσ)
        · refine Subgroup.zpowers_le.mpr ?_
          exact MulAction.mem_stabilizer_iff.mpr (hrhoA y hy)
      rw [hmemOf B]
      intro σ hσ
      exact MulAction.mem_stabilizer_iff.mp (hstab hσ)
    · intro y hy
      rw [hmemOf A]
      intro σ hσ
      exact (hmemOf B).mp hy σ (Subgroup.mem_sup_left hσ)
  -- ## `A = B` by Artin's theorem
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
  -- ## `ρ v ∈ A`, i.e. `ρ v = ρ p₀` for some `p₀ ∈ P`
  have hmem : ρ vV ∈ A := by
    rw [hAB]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (ρ vV))
  obtain ⟨p₀, hp₀mem, hp₀eq⟩ := Subgroup.mem_map.mp hmem
  have hp₀P : ((p₀ : ↥(Submission.Blueprint.centD H t)) : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp hp₀mem
  -- ## conclude `v = p₀ · (p₀⁻¹ v)` with `p₀⁻¹ v ∈ W`
  have hWmem : ((p₀ : ↥(Submission.Blueprint.centD H t)) : G)⁻¹ * v ∈ Work.ThmF.W H t := by
    have h1 : (p₀⁻¹ * vV : ↥(Submission.Blueprint.centD H t)) ∈
        (Work.ThmF.W H t).subgroupOf (Submission.Blueprint.centD H t) := by
      rw [← hker, MonoidHom.mem_ker]
      show ρ (p₀⁻¹ * vV) = 1
      rw [map_mul, map_inv, hp₀eq, inv_mul_cancel]
    simpa using Subgroup.mem_subgroupOf.mp h1
  rw [Set.mem_mul]
  exact ⟨((p₀ : ↥(Submission.Blueprint.centD H t)) : G), hp₀P,
    ((p₀ : ↥(Submission.Blueprint.centD H t)) : G)⁻¹ * v, hWmem, by group⟩

/-! ## §3. The main theorem -/

/-- **`Z(U) ⊆ P`** for `U = O^{2'}(C_G(P))`, the first step of Peterfalvi II Ch. VII §4 (p. 278),
with `W H t ≠ ⊥` supplied as a hypothesis (so no rank-one black box is consumed). -/
theorem center_le_P {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hQ3 : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) (hW : Work.ThmF.W H t ≠ ⊥)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y)
    (hZV : (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
      (Work.PSU3.StageB.centralizerOddResidual P).subtype ≤ Submission.Blueprint.centD H t) :
    Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P) ≤
      P.subgroupOf (Work.PSU3.StageB.centralizerOddResidual P) := by
  classical
  -- ## the fixed-point-freeness of `W#` on `Q ∖ Q₀` (Ch. VI §1 case c)
  have hsem : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H :=
    Work.PSU3.StageA.V_caseC_W_semireg hS hC4 hHig hQ3
  -- ## `P` centralises `y`
  have hPy : ∀ p ∈ P, p * y = y * p := by
    intro p hp
    have h := hyc p hp
    calc p * y = p * (p⁻¹ * y * p) := by rw [h]
      _ = y * p := by group
  have hycent : y ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun p hp => hPy p hp)
  -- ## nothing nontrivial in `W` centralises `y`
  have hWy : ∀ w ∈ Work.ThmF.W H t, w * y = y * w → w = 1 := by
    intro w hwW hwy
    by_contra hw1
    exact hy0 (hsem w hwW hw1 y hyQ hwy)
  -- ## `P ⊓ W = ⊥`
  have hPW : P ⊓ Work.ThmF.W H t = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro p hp
    rw [Subgroup.mem_inf] at hp
    rw [Subgroup.mem_bot]
    by_contra hp1
    exact hp1 (hWy p hp.2 (hPy p hp.1))
  -- ## `y ∈ U`
  have hyU : y ∈ Work.PSU3.StageB.centralizerOddResidual P :=
    mem_centralizerOddResidual_of_mem_Q hS hyQ hycent
  -- ## the Galois step (`z` fixes `C_{Q₀}(P)` pointwise ⟹ `z ∈ P · W`)
  have hgalois := mem_mul_of_fixes_centralizer_Q0 hS hC4 hPV hPW hW
  -- ## assembly
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  have hzV : ((z : ↥(Work.PSU3.StageB.centralizerOddResidual P)) : G) ∈
      Submission.Blueprint.centD H t :=
    hZV (Subgroup.mem_map_of_mem _ hz)
  have hzcent : ∀ u : ↥(Work.PSU3.StageB.centralizerOddResidual P),
      (z : ↥(Work.PSU3.StageB.centralizerOddResidual P)) * u =
        u * z := fun u => (Subgroup.mem_center_iff.mp hz u).symm
  -- `z` fixes `C_{Q₀}(P)` pointwise
  have hzfix : ∀ x ∈ Work.ThmF.Q0sub H, x ∈ Subgroup.centralizer (P : Set G) →
      ((z : ↥(Work.PSU3.StageB.centralizerOddResidual P)) : G) * x = x *
        ((z : ↥(Work.PSU3.StageB.centralizerOddResidual P)) : G) := by
    intro x hxQ0 hxC
    have hxU : x ∈ Work.PSU3.StageB.centralizerOddResidual P :=
      mem_centralizerOddResidual_of_mem_Q hS (Q0sub_le_Q_of_hyp hS hxQ0) hxC
    exact congrArg Subtype.val (hzcent ⟨x, hxU⟩)
  -- `z ∈ P · W`
  obtain ⟨p, hpP, w, hwW, hpw⟩ := Set.mem_mul.mp (hgalois _ hzV hzfix)
  -- `w = p⁻¹ z` centralises `y`, hence is trivial
  have hzy : ((z : ↥(Work.PSU3.StageB.centralizerOddResidual P)) : G) * y =
      y * ((z : ↥(Work.PSU3.StageB.centralizerOddResidual P)) : G) :=
    congrArg Subtype.val (hzcent ⟨y, hyU⟩)
  have hwy : w * y = y * w := by
    have h1 : (p * w) * y = y * (p * w) := by
      rw [hpw, hzy]
    have hyw : y * (p * w) = p * (y * w) := by
      calc y * (p * w) = (y * p) * w := by group
        _ = (p * y) * w := by rw [hPy p hpP]
        _ = p * (y * w) := by group
    have h2 : p * (w * y) = p * (y * w) := by
      calc p * (w * y) = (p * w) * y := by group
        _ = y * (p * w) := h1
        _ = p * (y * w) := hyw
    exact mul_left_cancel h2
  have hw1 : w = 1 := hWy w hwW hwy
  have hzP : ((z : ↥(Work.PSU3.StageB.centralizerOddResidual P)) : G) ∈ P := by
    rw [← hpw, hw1, mul_one]
    exact hpP
  simpa using hzP

end Work.PSU3.StageB.NotFpfStep2
