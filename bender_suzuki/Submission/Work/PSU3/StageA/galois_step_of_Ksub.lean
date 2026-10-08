import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.mem_fixedField_iff_mem_centralizer
import Submission.Work.ThmF.ChV12.fixedField_card_pow
import Submission.Work.ThmF.ChV12.card_map_subgroupOf_eq
import Submission.Work.ThmF.ChV12.KsubSubgroupOfNormal
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_P

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

namespace Work.PSU3.StageA

/-- **The Galois step, phrased from `K = Kset` + cyclicity of `K`.**

This is the lemma `Work.PSU3.StageB.NotFpfStep2.mem_mul_of_fixes_centralizer_Q0` with the
hypothesis `W H t ≠ ⊥` (used there only to derive `Ksub H t = Kset H t` and
`IsCyclic ↥(Ksub H t)` via `Ksub_eq_Kset_of_W_ne_bot`) replaced by those two conclusions
themselves as hypotheses.

Ch. V §1 Prop. 3 identifies `Q₀` with the additive group of a finite field `F` on which
`V = C_D(t)` acts by field automorphisms with kernel `W`.  Consequently an element `v ∈ V` which
fixes `C_{Q₀}(P) = Q0sub H ⊓ C_G(P)` pointwise fixes the fixed field of the image `A` of `P` in
`Gal(F)`; Artin's theorem gives `A = A ⊔ ⟨ρ v⟩`, so `ρ v ∈ A`; as `P ⊓ W = 1` the group `P`
covers `A`, so `v ∈ P · W`. -/
theorem galois_step_of_Ksub {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t))
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t)
    (hPW : P ⊓ Work.ThmF.W H t = ⊥) :
    ∀ v ∈ Submission.Blueprint.centD H t,
      (∀ x ∈ Work.ThmF.Q0sub H, x ∈ Subgroup.centralizer (P : Set G) → v * x = x * v) →
      ∃ p ∈ P, ∃ w ∈ Work.ThmF.W H t, v = p * w := by
  classical
  intro v hvV hfixv
  -- ## structure identity data (`s`, `r`) and the identification `V = D ⊓ C_G(s)`
  obtain ⟨s, hsQ, hs2, r, hrQ, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hV : Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    Work.PSU3.StageA.centD_eq_centralizer_s hS hsQ hs2 hrQ hsr
  -- ## Ch. V §1 Prop. 3
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
  exact ⟨((p₀ : ↥(Submission.Blueprint.centD H t)) : G), hp₀P,
    ((p₀ : ↥(Submission.Blueprint.centD H t)) : G)⁻¹ * v, hWmem, by group⟩

end Work.PSU3.StageA
