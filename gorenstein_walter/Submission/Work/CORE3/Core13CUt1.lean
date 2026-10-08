import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aBothInvert
import Submission.Work.CORE3.Case1aThmCInputs
import Submission.Work.CORE3.Case1aFrattiniApi

namespace Work.CORE3

namespace Work.CORE3

open scoped Pointwise
open Subgroup
open Work.GW2

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

/-! ## Two elementary helpers -/

/-- If `a` commutes with `b`, then conjugating `b` by `a` fixes it. -/
private lemma c13ConjEqSelfOfCommute {G : Type*} [Group G] {a b : G} (h : Commute a b) :
    a * b * a⁻¹ = b := by
  have h' : a * b = b * a := h
  rw [h', mul_assoc, mul_inv_cancel, mul_one]

/-- `F(K) = F_{3'}(K) ⊔ O_3(K)`: the splitting of the Fitting subgroup at the prime `3`
(the Fitting subgroup is nilpotent, hence the product of its Sylow subgroups).

This is the statement `Work.CORE3.c1aFittingIn_eq_sup_three`; its proof is repeated here so
that `Core13CUt1` does not depend on a declaration of `Case1aThmCInputs` whose proof is not yet
complete (the rest of that file is used, and is axiom-clean). -/
private theorem c13FittingIn_eq_sup_three {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    fittingIn K = fittingPiIn ({3}ᶜ) K ⊔ pCoreIn 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ (sup_le (bfpf_fittingPiIn_le_fittingIn _ _) (c1aPcoreIn_le_fittingIn 3 K))
  rw [c1aFittingIn_eq_iSup_pCoreIn K]
  refine iSup_le fun q => ?_
  by_cases hq : (q : ℕ) = 3
  · rw [hq]; exact le_sup_right
  · refine le_sup_of_le_left ?_
    haveI hq' : Fact (Nat.Prime (q : ℕ)) := ⟨q.2⟩
    have hpi : Subgroup.IsPiSubgroup ({3}ᶜ) (Work.GW2.pCore (q : ℕ) ↥K) :=
      Subgroup.isPiSubgroup_of_isPGroup_of_mem
        (Work.CORE2A.pCore_isPGroup_of_finite (H := ↥K) (p := (q : ℕ)))
        (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hq)
    have h1 : Work.GW2.pCore (q : ℕ) ↥K ≤
        (Work.GW2.piCore ({3}ᶜ) ↥(Work.GW2.fitting ↥K)).map (Work.GW2.fitting ↥K).subtype :=
      Work.DSTR.FittingPiImg.le_map_piCore_of_le_of_normal (M := ↥K) ({3}ᶜ)
        (Work.CORE2A.pCore_le_fitting (G := ↥K) (p := (q : ℕ))) hpi
    exact Subgroup.map_mono (f := K.subtype) h1

/-- Design pass 13 §1, D6: `C_U(t₁) = C_U(S) ⊔ O_p(U)` in the §3a subcase `Ĥ = H` (no
commutation needed).

Route: the inclusion `C_U(S) ⊔ O_p(U) ≤ C_U(t₁)` is immediate (`t₁ ∈ B.S`, `D.cent`).
Conversely, for `u ∈ C_U(t₁)`, `U = F(U) ⊔ B` (`Work.CORE3.c1aU_eq_fitting_sup_B`, proved in
`Submission/Work/CORE3/Case1aThmCInputs.lean`) gives `u = f * b` with `f ∈ F(U)`, `b ∈ B`; `t₁`
centralizes `b`, hence `f`.  `F(U) = F_{3'}(U) ⊔ O_3(U)`
(`Work.CORE3.c1aFittingIn_eq_sup_three`, also in that file) gives `f = k * x` with
`k ∈ F_{3'}(U)`, `x ∈ O_3(U)`; `hInv.1` says `t₁` inverts `k` and `D.cent` (with `hp3 : D.p = 3`)
says it centralizes `x`, so `k⁻¹ * x = k * x`, whence `k² = 1` and `k = 1` (`F_{3'}(U) ≤ U` is
odd).  Hence `u = x * b ∈ O_p(U) ⊔ C_U(S)`. -/
theorem Core13CUt1 (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (hInv : Case1aBothInvertProp) (hFT : FeitThompsonProp) (hCtx : BenderCtx G)
    (B : BenderSetup G) (hCase1 : Case1 B) (hHhat : B.Hhat = B.H) (D : Case1aData B)
    (hp3 : D.p = 3) :
    B.U ⊓ centralizer ({D.t1} : Set G) =
      (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊔ pCoreIn D.p B.U := by
  classical
  refine le_antisymm ?_ ?_
  · -- `C_U(t₁) ≤ C_U(S) ⊔ O_p(U)`: the substantive inclusion
    intro u hu
    obtain ⟨huU, huC⟩ := Subgroup.mem_inf.mp hu
    -- `U = F(U) ⊔ C_U(S)`, and the second factor normalizes `F(U)`, so the join is the
    -- set-theoretic product; write `u = f * b`.
    have hdecomp : B.U =
        fittingIn B.U ⊔ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) :=
      c1aU_eq_fitting_sup_B I G hFT hCtx B hCase1
    have hFU : B.U ≤ Subgroup.normalizer (fittingIn B.U : Set G) := by
      have hN : (Work.GW2.fitting ↥B.U).Normal := Subgroup.normalCore_normal _
      have h := c1aLe_normalizer_map_subtype (K := B.U) (N := Work.GW2.fitting ↥B.U) hN
      simpa [Work.GW2.fittingIn] using h
    have hnorm : (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ≤
        Subgroup.normalizer (fittingIn B.U : Set G) := le_trans inf_le_left hFU
    have hprod := Subgroup.coe_mul_of_right_le_normalizer_left (fittingIn B.U)
      (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) hnorm
    have hu_mul : u ∈ (fittingIn B.U : Set G) *
        ((B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) : Subgroup G) : Set G) := by
      rw [← hprod, ← hdecomp]
      exact huU
    obtain ⟨f, hf, b, hb, hfb⟩ := Set.mem_mul.mp hu_mul
    -- `b` centralizes `t₁`, and `t₁` centralizes `u`, hence `t₁` centralizes `f = u * b⁻¹`.
    have hbC : b ∈ centralizer ({D.t1} : Set G) :=
      Subgroup.centralizer_le (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        exact hx ▸ D.t1_mem) hb.2
    have hcf : Commute f D.t1 := by
      have hcu : Commute u D.t1 := Subgroup.mem_centralizer_singleton_iff.mp huC
      have hcb : Commute b D.t1 := Subgroup.mem_centralizer_singleton_iff.mp hbC
      have hf_eq : f = u * b⁻¹ := by rw [← hfb]; group
      rw [hf_eq]
      exact hcu.mul_left hcb.inv_left
    -- `F(U) = F_{3'}(U) ⊔ O_3(U)`; `O_3(U)` normalizes `F_{3'}(U)`, so again a product:
    -- write `f = x * k`.
    have hF3n : fittingPiIn ({3}ᶜ) B.U ≤
        Subgroup.normalizer ((pCoreIn 3 B.U : Subgroup G) : Set G) :=
      (le_trans (le_trans (bfpf_fittingPiIn_le_fittingIn ({3}ᶜ) B.U) (c1aFittingIn_le B.U))
        (Subgroup.le_normalizer (H := B.U))).trans (c1aLe_normalizer_pCoreIn 3 B.U)
    have hprod3 := Subgroup.coe_mul_of_right_le_normalizer_left (pCoreIn 3 B.U)
      (fittingPiIn ({3}ᶜ) B.U) hF3n
    have hfmem : f ∈ (pCoreIn 3 B.U ⊔ fittingPiIn ({3}ᶜ) B.U : Subgroup G) := by
      rw [sup_comm, ← c13FittingIn_eq_sup_three B.U]
      exact hf
    have hfprod : f ∈ (pCoreIn 3 B.U : Set G) * (fittingPiIn ({3}ᶜ) B.U : Set G) := by
      rw [← hprod3]
      exact hfmem
    obtain ⟨x, hx3, k, hk, hxk⟩ := Set.mem_mul.mp hfprod
    have hkU : k ∈ B.U :=
      c1aFittingIn_le B.U (bfpf_fittingPiIn_le_fittingIn ({3}ᶜ) B.U hk)
    -- `t₁` inverts `k` and centralizes `x`.
    have hkinv : D.t1 * k * D.t1⁻¹ = k⁻¹ :=
      (hInv G hFT hCtx B hCase1 hHhat D).1 k hk
    have hxP : x ∈ pCoreIn D.p B.U := by rw [hp3]; exact hx3
    have hxcen : x ∈ centralizer ({D.t1} : Set G) := D.cent hxP
    have hcx : D.t1 * x * D.t1⁻¹ = x := by
      have h : x * D.t1 = D.t1 * x := Subgroup.mem_centralizer_singleton_iff.mp hxcen
      rw [← h]; group
    -- hence `x * k⁻¹ = x * k` and `k = 1` (as `k ∈ B.U` has odd order).
    have hcomm_f : D.t1 * f * D.t1⁻¹ = f := c13ConjEqSelfOfCommute hcf.symm
    have hcomm_xk : D.t1 * f * D.t1⁻¹ = x * k⁻¹ := by
      rw [← hxk]
      calc D.t1 * (x * k) * D.t1⁻¹
          = (D.t1 * x * D.t1⁻¹) * (D.t1 * k * D.t1⁻¹) := by group
        _ = x * k⁻¹ := by rw [hcx, hkinv]
    have hxk_eq : x * k⁻¹ = x * k := by rw [← hcomm_xk, hcomm_f, ← hxk]
    have hk_eq : k⁻¹ = k := mul_left_cancel hxk_eq
    have hksq : k * k = 1 := by
      have h := mul_inv_cancel k
      rwa [hk_eq] at h
    have hk1 : k = 1 :=
      c1aEqOneOfMulSelfOdd (Work.CORE2A.bSetup_U_odd B) hkU hksq
    -- conclude `u = x * b ∈ O_p(U) ⊔ C_U(S)`
    have hufinal : u = x * b := by rw [← hfb, ← hxk, hk1, mul_one]
    rw [hufinal, sup_comm]
    exact Subgroup.mul_mem_sup hxP hb
  · -- `C_U(S) ⊔ O_p(U) ≤ C_U(t₁)`
    refine sup_le ?_ ?_
    · exact le_inf inf_le_left (le_trans inf_le_right (Subgroup.centralizer_le (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        exact hx ▸ D.t1_mem)))
    · exact le_inf (c1aPcoreIn_le_self D.p B.U) D.cent

end Work.CORE3

open Subgroup
open Work.GW2

/-- The same lemma under the name used by the consumers of this module
(`Work.CORE3.Core13CUt1`), the inner namespace of the skeleton being kept as well. -/
theorem Core13CUt1 (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (hInv : Case1aBothInvertProp) (hFT : FeitThompsonProp) (hCtx : BenderCtx G)
    (B : BenderSetup G) (hCase1 : Case1 B) (hHhat : B.Hhat = B.H) (D : Case1aData B)
    (hp3 : D.p = 3) :
    B.U ⊓ centralizer ({D.t1} : Set G) =
      (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊔ pCoreIn D.p B.U :=
  _root_.Work.CORE3.Work.CORE3.Core13CUt1 G I hInv hFT hCtx B hCase1 hHhat D hp3

end Work.CORE3
