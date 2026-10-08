/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4)

# `C_H(s) = C_U(s) · C_S(s)` for `s ∈ S \ S₀` (Bender p. 219, 227)

Bender 1981, p. 219 fixes `S` a dihedral Sylow 2-subgroup of `G`, `S₀ ≤ S` cyclic of index two,
`t` the involution of `S₀`, `H = C_G(t)` and `U = O(H)`, and recalls that `H = S U`.  For
`s ∈ S \ S₀` one has

* `C_S(s) = {1, t, s, s t}` (Klein four-group), so `|C_S(s)| = 4`;
* `C_H(s) = C_U(s) · C_S(s)`, because `H = U · S`, `U ⊓ S = ⊥` and `U ⊴ H`.

Counting orders (`|H| = |U| · |S|`, `|S| = 2 |S₀|`) therefore gives

  `2 · |H : C_H(s)| = |S₀| · |U : C_U(s)|`,

which is the form used at p. 227 in Bender's Theorem A bound.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.CardCentralizerComplIndexTwo
import Submission.Work.CORE4.CentralizerInfEqSup

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-- Arithmetic step of the index count below: if `a · (c · 4) = u · (2 s₀)` and `b · c = u`, then
`2 a = s₀ · b` (the equalities come from `|H| = |U| · |S|`, `|H : C_H(s)| · |C_H(s)| = |H|`,
`|S| = 2 |S₀|`, `|C_H(s)| = |C_U(s)| · 4` and `|U : C_U(s)| · |C_U(s)| = |U|`). -/
private theorem arith_helper (a b u s0 c : ℕ) (hc : 0 < c)
    (h1 : a * (c * 4) = u * (2 * s0)) (h2 : b * c = u) : 2 * a = s0 * b := by
  have h1' : (a : ℤ) * ((c : ℤ) * 4) = (u : ℤ) * (2 * (s0 : ℤ)) := by exact_mod_cast h1
  have h2' : (b : ℤ) * c = u := by exact_mod_cast h2
  have hkey : ((2 * a : ℕ) : ℤ) = ((s0 * b : ℕ) : ℤ) := by push_cast; nlinarith
  exact_mod_cast hkey

/-- Bender p. 219 and 227: for an involution `s ∈ S \ S₀` of the dihedral Sylow 2-subgroup `S`
of `H = U·S` (with `t` central in `S` and `U ⊓ S = ⊥`), `C_H(s) = C_U(s)·C_S(s)` and
`|C_S(s)| = 4`, so `2·|H : C_H(s)| = |S₀| · |U : C_U(s)|`. -/
theorem Case2CHs :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
      (h : Work.GW2.Case2Ctx B) (s : G), s ∈ (B.S : Subgroup G) → s ∉ B.S0 →
      2 * ((B.H ⊓ Subgroup.centralizer ({s} : Set G)).relIndex B.H) =
        Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({s} : Set G)).relIndex B.U := by
  intro G _ _ I B h s hsS hs0
  -- `C = C_G(s)`
  set C : Subgroup G := Subgroup.centralizer ({s} : Set G) with hCdef
  -- §4 (9) plus `I.toolkit.l2syl`: `S` is dihedral, `S ≃* DihedralGroup n`, `n ≥ 2`.
  obtain ⟨n, hn2, hdih⟩ := h.sylow_dihedral I
  obtain ⟨e⟩ := hdih
  have hcardS : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  -- `|S₀| = n` and `|S| = 2 |S₀|`
  have hcardS0 : Nat.card ↥B.S0 = n := by
    have hh := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [inf_eq_left.mpr B.S0_le, B.S0_index, hcardS] at hh
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) hh
  have hcardS' : Nat.card ↥(B.S : Subgroup G) = 2 * Nat.card ↥B.S0 := by
    rw [hcardS0]; exact hcardS
  -- `n` is even, because `S₀` contains the involution `t`
  have hnEven : Even n := by
    rw [even_iff_two_dvd, ← hcardS0]
    simpa [B.t_order] using Subgroup.orderOf_dvd_natCard B.S0 B.t_mem
  -- `|C_S(s)| = 4`
  have hcardCS : Nat.card ↥((B.S : Subgroup G) ⊓ C) = 4 :=
    CardCentralizerComplIndexTwo n hn2 hnEven (B.S : Subgroup G) B.S0 B.S0_le B.S0_index
      B.S0_cyclic ⟨e⟩ s hsS hs0
  -- `C_H(s) = C_U(s) ⊔ C_S(s)` (Bender p. 219: `H = U · S`)
  have hdec : B.H ⊓ C = (B.U ⊓ C) ⊔ ((B.S : Subgroup G) ⊓ C) :=
    CentralizerInfEqSup B.U (B.S : Subgroup G) B.H (h.H_eq_U_sup_S I) B.U_inf_S B.U_normal s hsS
  have hAU : B.U ⊓ C ≤ B.H ⊓ C :=
    le_inf (le_trans inf_le_left B.U_le_H) inf_le_right
  have hBS : (B.S : Subgroup G) ⊓ C ≤ B.H ⊓ C :=
    le_inf (le_trans inf_le_left B.S_le_H) inf_le_right
  -- `U ⊓ C ⊴ H ⊓ C` (as `U ⊴ H` and `C` is a subgroup)
  have hnorm' : ((B.U ⊓ C).subgroupOf (B.H ⊓ C)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAU]
    intro a b ha hb
    obtain ⟨haU, haC⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨hbH, hbC⟩ := Subgroup.mem_inf.mp hb
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal a b haU hbH,
        C.mul_mem (C.mul_mem hbC haC) (C.inv_mem hbC)⟩
  have hbot : (B.U ⊓ C) ⊓ ((B.S : Subgroup G) ⊓ C) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxU, -⟩ := Subgroup.mem_inf.mp h1
    obtain ⟨hxS, -⟩ := Subgroup.mem_inf.mp h2
    exact Subgroup.mem_bot.mp (by rw [← B.U_inf_S]; exact Subgroup.mem_inf.mpr ⟨hxU, hxS⟩)
  -- `|C_H(s)| = |C_U(s)| · 4` (second isomorphism theorem)
  have hcardHC : Nat.card ↥(B.H ⊓ C) = Nat.card ↥(B.U ⊓ C) * 4 := by
    have hkey := relIndex_eq_relIndex_inf_of_normal_sup_eq (B.U ⊓ C) ((B.S : Subgroup G) ⊓ C)
      (B.H ⊓ C) hAU hBS hdec.symm hnorm'
    rw [hbot, Subgroup.relIndex_bot_left] at hkey
    have hmul := Subgroup.relIndex_mul_card ((B.S : Subgroup G) ⊓ C) (B.H ⊓ C)
    rw [hkey, inf_eq_left.mpr hBS, hcardCS] at hmul
    exact hmul.symm
  -- `|H| = |U| · |S|`
  have hcardH : Nat.card ↥B.H = Nat.card ↥B.U * Nat.card ↥(B.S : Subgroup G) := by
    have hh := Subgroup.relIndex_mul_card B.U B.H
    rw [inf_eq_left.mpr B.U_le_H, h.relIndex_U_H I] at hh
    rw [← hh, mul_comm]
  -- Lagrange in `H` and in `U`
  have hrelH : (B.H ⊓ C).relIndex B.H * Nat.card ↥(B.H ⊓ C) = Nat.card ↥B.H := by
    have hh := Subgroup.relIndex_mul_card (B.H ⊓ C) B.H
    rwa [inf_eq_left.mpr inf_le_left] at hh
  have hrelU : (B.U ⊓ C).relIndex B.U * Nat.card ↥(B.U ⊓ C) = Nat.card ↥B.U := by
    have hh := Subgroup.relIndex_mul_card (B.U ⊓ C) B.U
    rwa [inf_eq_left.mpr inf_le_left] at hh
  have h1 : (B.H ⊓ C).relIndex B.H * (Nat.card ↥(B.U ⊓ C) * 4) =
      Nat.card ↥B.U * (2 * Nat.card ↥B.S0) := by
    rw [← hcardHC, ← hcardS', ← hcardH]
    exact hrelH
  exact arith_helper _ _ _ _ _ Nat.card_pos h1 hrelU

end Work.CORE4
