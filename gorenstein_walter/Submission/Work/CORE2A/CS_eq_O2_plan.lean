/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE2A.exists_mul_of_mem_involutionSet_H

/-!
# CORE2A: plan for the middle conjunct of Bender's Theorem 2.6

This module contains a planning comment for `Work.CORE2A.thm26a_CS_eq_O2` (the middle conjunct
`S ⊓ C_G(U) = O₂(Ĥ)` of `Thm26Concl`) together with two proved helper facts.

## Bender 1981, p. 220 (first paragraph of the proof of Theorem 2.6)

> "Suppose `1 ≠ O₂(Ĥ)`.  Then `U` centralizes `O₂(Ĥ)` and hence equals `O(Ĥ)`.  Now the
> assertion follows immediately because all involutions in `C_S(U)` are conjugate in
> `N_G(U) = Ĥ` and `Ĥ` has at least two classes of involutions by Lemma 2.1."

## The route used here

Write `V := pCoreIn 2 B.Hhat = O₂(Ĥ)` and `Q := (B.S : Subgroup G) ⊓ C_G(B.U)`.

* **Step 0 (`V ≤ Q`).**  `V ≤ S` (`Work.CORE2A.pCoreIn_le_S`); and `V ≤ C_G(U)` because
  `V ≤ S ≤ H` with `V ⊴ H` (`conj_mem_pCoreIn`) and `U ⊴ H`, so `[U,V] ≤ U ⊓ V = ⊥`
  (`U` is odd, `V` is a `2`-group).  This is `V_le_centralizer_U` below.

* **`Q ≠ S`.**  If `Q = S`, then `S ≤ C_G(U)`; then configuration (a) of Lemma 2.2 holds
  (`S₀ ≤ C_G(U)`), and for `s ∈ S − S₀` the set `I_U(s)` is trivial, so (b) and (c) hold as
  well — contradicting `h22`.  This is `CS_ne_S` below.  Hence `Q < S`.

* **The two cases for `V` relative to `S₀`.**

  *Case* `V ≤ S₀`.  Then `Ĥ = H = C_G(t)` (`Work.CORE2A.Hhat_eq_H_of_pCoreIn_le_S0`), hence
  `V = O₂(H)`.  Also `V = core_H(S₀)` (`V ⊴ H`, `V ≤ S₀`, and the core is a normal `2`-subgroup
  of `H`).  `H = U ⋊ S` is solvable (`U` odd, so solvable by `hFT`; `S` a `2`-group); by
  P. Hall's theorem `C_H(F(H)) ≤ F(H)` (`OddOrder.GroupTheory.centralizer_fitting_le_fitting`)
  and `F(H) = O₂(H)·O_{2'}(F(H))` with `O₂(H) = V`.  Every `x ∈ Q` lies in `S₀` (an element of
  `Q − S₀` is a reflection, hence an involution, and every involution of `Q` lies in `V ⊆ S₀`),
  so `x` commutes with `V ≤ S₀`; together with `x ∈ C_G(U) ⊇ C_G(O_{2'}(F(H)))` this gives
  `x ∈ C_H(F(H)) ≤ F(H)`, and `x` is a `2`-element of `F(H)`, so `x ∈ O₂(H) = V`.  Thus
  `Q ≤ V`.  (Equivalently: show `V = S₀`; then `Q ⊇ V = S₀ ⊴ S`, `Q ≤ S` and `Q ≠ S` give
  `Q = S₀ = V` since the only subgroups of `S` containing the index-two subgroup `S₀` are `S₀`
  and `S`.)

  *Case* `V ⊄ S₀`.  Since `V ≤ Q ≤ S` and `V ⊴ Ĥ ⊇ S`, there is `v ∈ V` with `v ∉ S₀`, so `v`
  is an involution of `Q`; if `V = S` then `Q = V` is immediate, and otherwise `V` has index
  `2` in `S`, and `Q ≠ S` forces `Q = V`.

`CS_eq_O2_le_of_le_S0` and `CS_eq_O2_le_of_not_le_S0` are these two cases; the main theorem
`Work.CORE2A.thm26a_CS_eq_O2` is their assembly with `V ≤ Q`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

section Helpers

variable {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)

/-- **`O₂(Ĥ) ≤ C_G(U)`** (Bender p. 220: "`U` centralizes `O₂(Ĥ)`").
`V = O₂(Ĥ) ≤ S ≤ H` is normalised by `H` and `U ⊴ H`; since `U` has odd order and `V` is a
`2`-group, `[U,V] ≤ U ⊓ V = ⊥`. -/
theorem V_le_centralizer_U :
    Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  haveI : (B.U.subgroupOf B.H).Normal := subgroupOf_oddCoreIn_normal B.H
  have hvH : v ∈ B.H := bSetup_S_le_H B (pCoreIn_le_S B hv)
  have huH : u ∈ B.H := bSetup_U_le_H B hu
  have huHhat : u ∈ B.Hhat := B.H_le_Hhat huH
  have huinvH : u⁻¹ ∈ B.H := B.H.inv_mem huH
  -- `v * u⁻¹ * v⁻¹ ∈ U`
  have hconj : (⟨v, hvH⟩ * ⟨u⁻¹, huinvH⟩ * (⟨v, hvH⟩)⁻¹ : ↥B.H)
      ∈ B.U.subgroupOf B.H :=
    Subgroup.Normal.conj_mem inferInstance ⟨u⁻¹, huinvH⟩
      (Subgroup.mem_subgroupOf.mpr (B.U.inv_mem hu)) ⟨v, hvH⟩
  have hU1 : v * u⁻¹ * v⁻¹ ∈ B.U := by
    have := Subgroup.mem_subgroupOf.mp hconj
    simpa using this
  -- `u * v * u⁻¹ * v⁻¹ ∈ U` and `∈ V`, so it is `1`
  have hU : u * v * u⁻¹ * v⁻¹ ∈ B.U := by
    have h : u * (v * u⁻¹ * v⁻¹) ∈ B.U := B.U.mul_mem hu hU1
    simpa [mul_assoc] using h
  have hV : u * v * u⁻¹ * v⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat :=
    (Work.GW2.pCoreIn 2 B.Hhat).mul_mem
      (conj_mem_pCoreIn B huHhat hv) ((Work.GW2.pCoreIn 2 B.Hhat).inv_mem hv)
  have hbot : B.U ⊓ Work.GW2.pCoreIn 2 B.Hhat = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup_two (bSetup_U_odd B) (pCoreIn_isPGroup B)
  have hone : u * v * u⁻¹ * v⁻¹ = 1 := by
    have hmem : u * v * u⁻¹ * v⁻¹ ∈ B.U ⊓ Work.GW2.pCoreIn 2 B.Hhat := ⟨hU, hV⟩
    rw [hbot] at hmem
    simpa using hmem
  have hconj2 : u * v * u⁻¹ = v := by
    have h := congrArg (fun z => z * v) hone
    simpa [mul_assoc] using h
  calc u * v = u * v * u⁻¹ * u := by group
    _ = v * u := by rw [hconj2]

/-- **`Q ≠ S`** where `Q = S ⊓ C_G(U)`: if `Q = S` then `S ≤ C_G(U)`, and Bender's
configuration of Lemma 2.2 holds (with `S₀ ≤ C_G(U)` and `I_U(s) = 1` for `s ∈ S − S₀`),
contradicting `h22`. -/
theorem CS_ne_S (h22 : Work.GW2.Lemma22Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) :
    (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) ≠ (B.S : Subgroup G) := by
  intro hQ
  have hSU : (B.S : Subgroup G) ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← hQ]; exact inf_le_right
  have ha : B.S0 ≤ Subgroup.centralizer (B.U : Set G) := le_trans B.S0_le hSU
  obtain ⟨s, hsS, hs0⟩ := bSetup_exists_mem_S_not_mem_S0 B
  have hsC : s ∈ Subgroup.centralizer (B.U : Set G) := hSU hsS
  -- every element of `I_U(s)` is `1`
  have hmem1 : ∀ y ∈ Work.GW2.invSet B.U s, y = 1 := by
    rintro y ⟨hyU, hyinv⟩
    have hcomm : y * s = s * y := (Subgroup.mem_centralizer_iff.mp hsC) y hyU
    have hy1 : y = y⁻¹ := by
      have h : s * y * s⁻¹ = y := by rw [hcomm.symm]; group
      rw [← hyinv, h]
    have hy2 : y * y = 1 := by
      have h : y * y = y * y⁻¹ := congrArg (fun z => y * z) hy1
      rw [h, mul_inv_cancel]
    have hodd : Odd (orderOf y) :=
      Odd.of_dvd_nat (bSetup_U_odd B) (Subgroup.orderOf_dvd_natCard B.U hyU)
    have hdvd : orderOf y ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hy2
    exact orderOf_eq_one_iff.mp ((hodd.coprime_two_right).eq_one_of_dvd hdvd)
  have hIset : ((⊥ : Subgroup G) : Set G) = Work.GW2.invSet B.U s := by
    ext y
    constructor
    · intro hy
      have hy1 : y = 1 := by simpa using hy
      rw [hy1]
      exact one_mem_invSet (s := s) (B.U.one_mem)
    · intro hy
      have hy1 : y = 1 := hmem1 y hy
      rw [hy1]
      exact Subgroup.mem_bot.mpr rfl
  refine (Work.CORE2A.lemma22Prop_iff.mp h22) G hFT hctx B ⟨ha, s, hsS, hs0, ⊥, hIset, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]; infer_instance
  · intro X hX hXI
    rw [le_bot_iff] at hXI
    exact absurd hXI hX

end Helpers

end Work.CORE2A
