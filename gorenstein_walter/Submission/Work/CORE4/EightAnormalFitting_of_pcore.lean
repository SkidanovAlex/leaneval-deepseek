/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# The `A ⊴ F(U)` step of Bender 1981, §4 (8), p. 226

Bender's §4 (8) states, for the odd prime `p` with `P ≤ F` of order `p` and `A` the unique
subgroup of type `(p,p)` of `F × K₁`:

> `|U : B₀ K F(U)| ≤ p`, and *(unless `I_U(s) ⊴ Ĥ`)* `u ≤ p` and `A ⊴ F(U)`.

The object layer supplies `A ≤ O_p(U)` and `A ⊴ O_p(U)` (via Bender's subgroup
`Q = Ω₁(Z₂(O_p(U)))`).  The remaining step is purely about the finite *nilpotent* group `F(U)`
and holds in complete generality:

* `O_p(U)` is the Sylow `p`-subgroup of `F(U)`: every element of `F(U)` of `p`-power order
  lies in `O_p(U)` (`EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn` below; the Fitting subgroup
  is nilpotent, so a `p`-subgroup of it lies in its `p`-core, and the `p`-core of the normal
  subgroup `F(U) ⊴ U` lies in `O_p(U)`);
* in the nilpotent group `F(U)` two elements of coprime order commute, so a `p'`-element of
  `F(U)` centralizes `O_p(U) ⊇ A`.

Hence for `x ∈ F(U)` with `p`-part `a` and `p'`-part `b` (both in `⟨x⟩ ≤ F(U)`), conjugation by
`x = a b` acts on `A` as conjugation by `a ∈ O_p(U)`, which preserves `A`.

## Contents

* `EightANF_elem_decomp_pPart` — the elementary decomposition of `x` into a `p`-element and a `p'`-element
  (Bezout applied to `orderOf x = p ^ e * m`, `¬ p ∣ m`);
* `EightANF_le_pCore_of_normal_isPGroup` — a normal `p`-subgroup of a finite group lies in its `p`-core;
* `EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn` — every `p`-element of `F(K)` lies in `O_p(K)`;
* `EightAnormalFitting_of_pcore` — the target, `A ⊴ O_p(U)` and `A ≤ O_p(U)` give `A ⊴ F(U)`.
-/
import Mathlib
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Defs
import Submission.OddOrder.Isaacs.Ch01_Sylow.Basic
import Submission.Work.CORE4.A7VnotCyclicAux
import Submission.Work.CORE4.Case2SevenAux

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE4

open Work.GW2 Subgroup

variable {X : Type} [Group X] [Finite X]

/-! ## 0. `F(A)` is nilpotent (Fitting's theorem)

The Fitting subgroup `F(G) = ⟨N ⊴ G | N nilpotent⟩` of the vocabulary is the Fitting subgroup of
the odd-order library (the join of the `O_p(G)`, `p` ranging over the prime divisors of `|G|`),
which is nilpotent.  This is the only piece of group theory used below that is not in Mathlib. -/

/-- `Work.GW2.fitting` is the odd-order library's `OddOrder.Isaacs.Ch01.fitting`. -/
theorem EightANF_fitting_eq_fitting : Work.GW2.fitting X = OddOrder.Isaacs.Ch01.fitting X := by
  have hS : sSup {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N}
      = OddOrder.Isaacs.Ch01.fitting X := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hnil⟩
      haveI : N.Normal := hN
      haveI : Group.IsNilpotent ↥N := hnil
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · exact ⟨OddOrder.Isaacs.Ch01.fitting.normal X, OddOrder.Isaacs.Ch01.fitting.isNilpotent⟩
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

/-- **Fitting's theorem**: the Fitting subgroup `F(A)` of a subgroup `A` is nilpotent. -/
theorem EightANF_isNilpotent_fittingIn (A : Subgroup X) :
    Group.IsNilpotent ↥(Work.GW2.fittingIn A) := by
  haveI : Group.IsNilpotent ↥(Work.GW2.fitting ↥A) := by
    rw [EightANF_fitting_eq_fitting (X := ↥A)]
    exact OddOrder.Isaacs.Ch01.fitting.isNilpotent
  rw [show Work.GW2.fittingIn A = (Work.GW2.fitting ↥A).map A.subtype from rfl]
  exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective (Work.GW2.fitting ↥A)
    A.subtype A.subtype_injective)).mp inferInstance

/-! ## 1. The `p`-part/`p'`-part decomposition of an element -/

/-- **Decomposition of an element into a `p`-element and a `p'`-element.**

For a finite group `G`, a prime `p` and `x : G` there are `a b : G` with `a * b = x`, both `a`
and `b` powers of `x`, `⟨a⟩` a `p`-group and `orderOf b` coprime to `p`.

Write `orderOf x = p ^ e * m` with `¬ p ∣ m` and `1 = u * p ^ e + v * m` (Bezout); then
`a := x ^ (v * m)` has order dividing `p ^ e` and `b := x ^ (u * p ^ e)` has order dividing `m`. -/
theorem EightANF_elem_decomp_pPart {p : ℕ} (hp : p.Prime) (x : X) :
    ∃ a b : X, a * b = x ∧ a ∈ Subgroup.zpowers x ∧ b ∈ Subgroup.zpowers x ∧
      IsPGroup p ↥(Subgroup.zpowers a) ∧ (orderOf b).Coprime p := by
  have hn : orderOf x ≠ 0 := by
    rw [← Nat.card_zpowers x]
    exact Nat.card_pos.ne'
  obtain ⟨e, m, hm, hEq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : (p ^ e).Coprime m := Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.mpr hm)
  have hbez : (1 : ℤ) = ((p : ℤ) ^ e) * (p ^ e).gcdA m + (m : ℤ) * (p ^ e).gcdB m := by
    have h := Nat.gcd_eq_gcd_ab (p ^ e) m
    rw [hcop.gcd_eq_one] at h
    simpa using h
  have hsum : (p ^ e).gcdB m * (m : ℤ) + (p ^ e).gcdA m * ((p : ℤ) ^ e) = 1 := by
    linarith [hbez]
  refine ⟨x ^ ((p ^ e).gcdB m * (m : ℤ)), x ^ ((p ^ e).gcdA m * ((p : ℤ) ^ e)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← zpow_add, hsum, zpow_one]
  · exact Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩
  · exact Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩
  · apply IsPGroup.of_card_dvd_pow (n := e)
    rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]
    rw [← zpow_natCast, show ((p ^ e : ℕ) : ℤ) = (p : ℤ) ^ e from by push_cast; ring,
      ← zpow_mul]
    have h2 : ((p ^ e).gcdB m * (m : ℤ)) * ((p : ℤ) ^ e) =
        ((p ^ e * m : ℕ) : ℤ) * (p ^ e).gcdB m := by
      push_cast; ring
    rw [h2, zpow_mul, ← hEq, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have hdvd : orderOf (x ^ ((p ^ e).gcdA m * ((p : ℤ) ^ e))) ∣ m := by
      rw [orderOf_dvd_iff_pow_eq_one, ← zpow_natCast, ← zpow_mul]
      have h2 : ((p ^ e).gcdA m * ((p : ℤ) ^ e)) * (m : ℤ) =
          ((p ^ e * m : ℕ) : ℤ) * (p ^ e).gcdA m := by
        push_cast; ring
      rw [h2, zpow_mul, ← hEq, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact Nat.Coprime.coprime_dvd_left hdvd ((hp.coprime_iff_not_dvd.mpr hm).symm)

/-! ## 2. `p`-elements of the Fitting subgroup -/

/-- A normal `p`-subgroup of a finite group `H` lies in the `p`-core `O_p(H)`. -/
theorem EightANF_le_pCore_of_normal_isPGroup {H : Type*} [Group H] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup H} (hQ : Q.Normal) (hQp : IsPGroup p ↥Q) : Q ≤ Work.GW2.pCore p H := by
  haveI : (sSup {N : Subgroup H | N.Normal ∧ IsPGroup p N}).Normal :=
    Subgroup.sSup_normal _ (fun N hN => hN.1)
  rw [Work.GW2.pCore, Subgroup.normalCore_eq_self]
  exact le_sSup ⟨hQ, hQp⟩

/-- **Every `p`-element of the Fitting subgroup `F(K)` lies in `O_p(K)`.**

`x ∈ F(K)`, viewed in the nilpotent group `F(↥K)`, generates a `p`-subgroup, which lies in a
Sylow `p`-subgroup; Sylow subgroups of a nilpotent group are normal, hence inside the `p`-core
(`EightANF_le_pCore_of_normal_isPGroup`).  Mapping back to `G` gives `x ∈ O_p(F(K))`, and the `p`-core of
the normal subgroup `F(K) ⊴ K` is contained in `O_p(K)`. -/
theorem EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn (K : Subgroup X) (p : ℕ) (hp : p.Prime)
    {x : X} (hx : x ∈ Work.GW2.fittingIn K) (hxp : IsPGroup p ↥(Subgroup.zpowers x)) :
    x ∈ Work.GW2.pCoreIn p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn K) := EightANF_isNilpotent_fittingIn K
  have hxp' : IsPGroup p ↥(Subgroup.comap (Work.GW2.fittingIn K).subtype (Subgroup.zpowers x)) :=
    hxp.comap_of_injective (Work.GW2.fittingIn K).subtype (Work.GW2.fittingIn K).subtype_injective
  obtain ⟨Q, hQle⟩ := hxp'.exists_le_sylow
  have hQp : IsPGroup p ↥(Q : Subgroup ↥(Work.GW2.fittingIn K)) := Q.isPGroup'
  have hQcore : (Q : Subgroup ↥(Work.GW2.fittingIn K)) ≤
      Work.GW2.pCore p ↥(Work.GW2.fittingIn K) :=
    EightANF_le_pCore_of_normal_isPGroup (Q := (Q : Subgroup ↥(Work.GW2.fittingIn K))) inferInstance hQp
  have hx' : (⟨x, hx⟩ : ↥(Work.GW2.fittingIn K)) ∈
      Subgroup.comap (Work.GW2.fittingIn K).subtype (Subgroup.zpowers x) := by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_zpowers x
  have hxpc : x ∈ Work.GW2.pCoreIn p (Work.GW2.fittingIn K) := by
    rw [Work.GW2.pCoreIn]
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hQcore (hQle hx'), rfl⟩
  exact (Work.CORE4.pCoreIn_le_pCoreIn_of_normal (Subgroup.map_subtype_le _)
    (Work.CORE4.fittingIn_subgroupOf_normal K) p) hxpc

/-! ## 3. The target -/

/-- **`A ⊴ F(U)` from `A ≤ O_p(U)` and `A ⊴ O_p(U)`** (Bender 1981, §4 (8), p. 226).

Let `x ∈ F(U)` and let `x = a b` be its decomposition into a `p`-element `a` and a `p'`-element
`b` (`EightANF_elem_decomp_pPart`), both powers of `x`, hence in `F(U)`.  By
`EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn`, `a ∈ O_p(U)`, so conjugation by `a` preserves `A`
(the hypothesis `A ⊴ O_p(U)`).  And `b` centralizes `O_p(U)`: `b` and any `z ∈ O_p(U)` lie in the
nilpotent group `F(U)` with coprime orders, and commute.  Hence conjugation by `x = a b` preserves
`A`, i.e. `F(U) ≤ N_G(A)`. -/
theorem EightAnormalFitting_of_pcore {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G}
    (p : ℕ) (hp : p.Prime) (A : Subgroup G)
    (hAle : A ≤ Work.GW2.fittingIn B.U) (hAp : IsPGroup p ↥A)
    (hAleOp : A ≤ Work.GW2.pCoreIn p B.U)
    (hAnOp : (A.subgroupOf (Work.GW2.pCoreIn p B.U)).Normal) :
    (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAle, Subgroup.le_normalizer_iff]
  intro x hx y hy
  obtain ⟨a, b, hab, ha, hb, hap, hbcop⟩ := EightANF_elem_decomp_pPart hp x
  have haF : a ∈ Work.GW2.fittingIn B.U := (Subgroup.zpowers_le.mpr hx) ha
  have hbF : b ∈ Work.GW2.fittingIn B.U := (Subgroup.zpowers_le.mpr hx) hb
  have haP : a ∈ Work.GW2.pCoreIn p B.U :=
    EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn B.U p hp haF hap
  have hay : a * y * a⁻¹ ∈ A :=
    (Subgroup.normal_subgroupOf_iff hAleOp).mp hAnOp y a hy haP
  have hby : b * y * b⁻¹ = y := by
    haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U) := EightANF_isNilpotent_fittingIn B.U
    have hyF : y ∈ Work.GW2.fittingIn B.U := hAle hy
    have hcomm : Commute (⟨b, hbF⟩ : ↥(Work.GW2.fittingIn B.U))
        (⟨y, hyF⟩ : ↥(Work.GW2.fittingIn B.U)) := by
      apply Group.IsNilpotent.commute_of_orderOf_coprime
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp (Work.CORE4.isPGroup_pCoreIn p B.U))
        (⟨y, hAleOp hy⟩ : ↥(Work.GW2.pCoreIn p B.U))
      have hyk : orderOf y ∣ p ^ k := by rw [Subgroup.orderOf_mk] at hk; exact hk
      exact (hbcop.pow_right k).coprime_dvd_right hyk
    have h1 : b * y = y * b := by simpa using congrArg Subtype.val hcomm.eq
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : x * y * x⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by rw [← hab]; group
  rw [hmem, hby]
  exact hay

end Work.CORE4
