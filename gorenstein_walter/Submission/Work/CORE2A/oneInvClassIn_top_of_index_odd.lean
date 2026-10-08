/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.inf_centralizer_eq_center_map

/-!
# CORE2A: one involution class in `K` from one involution class in `E`, `[K : E·C_K(E)]` odd

Let `K` be a finite group, `E ≤ K`, and `C = C_K(E) ⊴ K`.  Suppose that

* `Z(E)` has odd order and `C` has odd order;
* `[K : E·C]` is odd (equivalently: the image `Ē = EC/C` has odd index in `K/C`);
* the involutions of `E` form a single class under conjugation by elements of `E`
  (`Work.GW2.C3OneInvClassIn E`).

Then the involutions of `K` form a single class under conjugation by elements of `K`
(`Work.GW2.OneInvClassIn (⊤ : Subgroup K)`).

The proof has two independent halves.

* *The involutions of `E·C` lie in `E`.*  Write `x = e·c` with `e ∈ E`, `c ∈ C` (this uses
  `C ⊴ K`).  Since `c` centralizes `e`, `x ^ 2 = e ^ 2 * c ^ 2`, so `e ^ 2 = (c ^ 2)⁻¹` lies in
  `E ∩ C`, which is the image of `Z(E)` in `K`.  As `Z(E)` has odd order, `e ^ 2` has a square
  root `z` in `Z(E)`; replacing `e` by `t = e·z` (still in `E`, and `t ^ 2 = 1`) does not change
  the coset modulo `C`, so `x = t·c₁` with `c₁ ∈ C`.  Now `t` and `c₁` commute, so
  `1 = x ^ 2 = t ^ 2 · c₁ ^ 2 = c₁ ^ 2`, whence `c₁ = 1` because `C` has odd order, and `x = t ∈ E`.
* *Every involution of `K` is `K`-conjugate into `E`.*  Since `[K : E·C]` is odd, `E·C` is a
  subgroup of odd index, so a Sylow `2`-subgroup `S₀` of `E·C`, viewed inside `K`, has odd index
  and hence is a Sylow `2`-subgroup of `K` (`IsPGroup.toSylow`).  An involution `x ∈ K` lies in
  some Sylow `2`-subgroup of `K` (`IsPGroup.exists_le_sylow`), which is conjugate to that Sylow
  (`Sylow.isPretransitive_of_finite`), so `g x g⁻¹ ∈ E·C`, and the first half puts it in `E`.

The two halves are glued by the definition of `Work.GW2.OneInvClassIn`.
-/

set_option linter.style.haveILetI false

namespace Work.CORE2A

open Subgroup
open scoped Pointwise

/-! ## Elementary arithmetic helpers -/

/-- In a finite group of odd order the squaring map is surjective: with `|H| = 2m+1` one has
`x = (x ^ (m+1)) ^ 2`. -/
private theorem sq_surjective_of_odd_card {H : Type*} [Group H] [Finite H]
    (h : Odd (Nat.card H)) : Function.Surjective (fun x : H => x ^ 2) := by
  obtain ⟨m, hm⟩ := h
  haveI := Fintype.ofFinite H
  have hc : Fintype.card H = 2 * m + 1 := by rw [← Nat.card_eq_fintype_card]; exact hm
  intro x
  refine ⟨x ^ (m + 1), ?_⟩
  change (x ^ (m + 1)) ^ 2 = x
  rw [← pow_mul, show (m + 1) * 2 = Fintype.card H + 1 by rw [hc]; ring, pow_succ,
    pow_card_eq_one, one_mul]

/-- A finite group of odd order has no element of order two. -/
private theorem eq_one_of_sq_eq_one_of_odd_card {H : Type*} [Group H] [Finite H]
    (h : Odd (Nat.card H)) {x : H} (hx : x ^ 2 = 1) : x = 1 := by
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx
  have hdvdn : orderOf x ∣ Nat.card H := orderOf_dvd_natCard x
  have hodd : ¬ (2 ∣ Nat.card H) :=
    fun h2 => (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h2 ▸ hdvdn) hodd

/-- `(E·C)/C` has the same index in `K/C` as `E·C` has in `K`. -/
private theorem index_map_mk'_eq_index_sup {K : Type} [Group K] (E C : Subgroup K) [C.Normal] :
    (E.map (QuotientGroup.mk' C)).index = (E ⊔ C).index := by
  have h := Subgroup.index_map E (QuotientGroup.mk' C)
  rw [QuotientGroup.ker_mk'] at h
  rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective C), Subgroup.index_top,
    mul_one] at h
  exact h

/-! ## Involutions of `E ⊔ C` lie in `E` -/

/-- **The core membership step.**  If `x ∈ E ⊔ C` and `x ^ 2 = 1`, then `x ∈ E`. -/
private theorem mem_of_mem_sup_of_sq_eq_one {K : Type} [Group K] [Finite K] (E C : Subgroup K)
    (hC : C = Subgroup.centralizer (E : Set K)) [hCn : C.Normal]
    (hZodd : Odd (Nat.card (Subgroup.center ↥E))) (hCodd : Odd (Nat.card C))
    {x : K} (hx : x ∈ E ⊔ C) (hx2 : x ^ 2 = 1) : x ∈ E := by
  obtain ⟨e, heE, c, hcC, hxc⟩ := (Subgroup.mem_sup_of_normal_right (s := E) (t := C)).mp hx
  have hx2' : (e * c) ^ 2 = 1 := by rw [hxc]; exact hx2
  -- `c` centralizes `E`, so `c` commutes with `e`
  have hce : Commute e c :=
    Subgroup.mem_centralizer_iff.mp (hC ▸ hcC) e heE
  -- `e ^ 2 = (c ^ 2)⁻¹`
  have he2 : e ^ 2 = (c ^ 2)⁻¹ := by
    have h : (e * c) ^ 2 = e ^ 2 * c ^ 2 := hce.mul_pow 2
    rw [hx2'] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have he2mem : e ^ 2 ∈ E ⊓ C :=
    ⟨E.pow_mem heE 2, by rw [he2]; exact C.inv_mem (C.pow_mem hcC 2)⟩
  -- `E ⊓ C` is the image of the centre of `E`
  have hsup : E ⊓ C = (Subgroup.center ↥E).map E.subtype := by
    rw [hC]; exact inf_centralizer_eq_center_map E
  have hZleE : (Subgroup.center ↥E).map E.subtype ≤ E := Subgroup.map_subtype_le _
  have hZleC : (Subgroup.center ↥E).map E.subtype ≤ C := by
    rintro z ⟨y, hy, rfl⟩
    rw [hC]
    intro a ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨a, ha⟩)
  have he2Z : e ^ 2 ∈ (Subgroup.center ↥E).map E.subtype := hsup ▸ he2mem
  have hZodd' : Odd (Nat.card ↥((Subgroup.center ↥E).map E.subtype)) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]; exact hZodd
  -- a square root `w` of `(e ^ 2)⁻¹` inside the centre of `E`
  obtain ⟨w, hw⟩ := sq_surjective_of_odd_card (H := ↥((Subgroup.center ↥E).map E.subtype))
    hZodd' ⟨(e ^ 2)⁻¹, (Subgroup.inv_mem _) he2Z⟩
  have hwK : ((w : K)) ^ 2 = (e ^ 2)⁻¹ := by
    have h := congrArg (fun t : ↥((Subgroup.center ↥E).map E.subtype) => (t : K)) hw
    simpa using h
  have hwE : (w : K) ∈ E := hZleE w.2
  have hwC : (w : K) ∈ C := hZleC w.2
  have hwe : Commute e (w : K) :=
    Subgroup.mem_centralizer_iff.mp (hC ▸ hwC) e heE
  -- `t = e * w` is an involution of `E` with the same image as `x` in `K ⧸ C`
  have ht2 : (e * (w : K)) ^ 2 = 1 := by
    have h : (e * (w : K)) ^ 2 = e ^ 2 * (w : K) ^ 2 := hwe.mul_pow 2
    rw [h, hwK, mul_inv_cancel]
  -- hence `x = t * c₁` with `c₁ = w⁻¹ * c ∈ C`
  have hc1C : (w : K)⁻¹ * c ∈ C := C.mul_mem (C.inv_mem hwC) hcC
  have hx_eq : e * c = (e * (w : K)) * ((w : K)⁻¹ * c) := by group
  have hc1sq : ((w : K)⁻¹ * c) ^ 2 = 1 := by
    have htc1 : Commute (e * (w : K)) ((w : K)⁻¹ * c) :=
      Subgroup.mem_centralizer_iff.mp (hC ▸ hc1C) (e * (w : K)) (E.mul_mem heE hwE)
    have h : ((e * (w : K)) * ((w : K)⁻¹ * c)) ^ 2
        = (e * (w : K)) ^ 2 * ((w : K)⁻¹ * c) ^ 2 := htc1.mul_pow 2
    rw [← hx_eq, hx2', ht2, one_mul] at h
    exact h.symm
  have hc1one : (w : K)⁻¹ * c = 1 := by
    have hsub : (⟨(w : K)⁻¹ * c, hc1C⟩ : ↥C) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hc1sq
    have h1 := eq_one_of_sq_eq_one_of_odd_card (H := ↥C) hCodd hsub
    simpa using congrArg (fun z : ↥C => (z : K)) h1
  have hmem : e * c ∈ E := by
    rw [hx_eq, hc1one, mul_one]
    exact E.mul_mem heE hwE
  rwa [hxc] at hmem

/-! ## The lemma -/

theorem oneInvClassIn_top_of_index_odd {K : Type} [Group K] [Finite K] (E C : Subgroup K)
    (hC : C = Subgroup.centralizer (E : Set K)) [hCn : C.Normal]
    (hZodd : Odd (Nat.card (Subgroup.center ↥E))) (hCodd : Odd (Nat.card C))
    (hidx : Odd ((E.map (QuotientGroup.mk' C)).index))
    (hE1 : Work.GW2.C3OneInvClassIn E) : Work.GW2.OneInvClassIn (⊤ : Subgroup K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `E ⊔ C` has odd index in `K`
  have hHidx : Odd (E ⊔ C).index := by
    rw [← index_map_mk'_eq_index_sup E C]; exact hidx
  -- a Sylow `2`-subgroup of `E ⊔ C`, viewed inside `K`, is a Sylow `2`-subgroup of `K`
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := ↥(E ⊔ C))
  have hSidx : ((S : Subgroup ↥(E ⊔ C)).map (E ⊔ C).subtype).index
      = (S : Subgroup ↥(E ⊔ C)).index * (E ⊔ C).index :=
    Subgroup.index_map_subtype (S : Subgroup ↥(E ⊔ C))
  have hSnotdvd : ¬ 2 ∣ ((S : Subgroup ↥(E ⊔ C)).map (E ⊔ C).subtype).index := by
    rw [hSidx]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h2
    · exact Sylow.not_dvd_index S h1
    · exact (Nat.not_even_iff_odd.mpr hHidx) (even_iff_two_dvd.mpr h2)
  let S' : Sylow 2 K := (S.isPGroup'.map (E ⊔ C).subtype).toSylow hSnotdvd
  have hS'le : (S' : Subgroup K) ≤ E ⊔ C := by
    show (S.isPGroup'.map (E ⊔ C).subtype).toSylow hSnotdvd ≤ E ⊔ C
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subtype_le _
  -- every involution of `K` is `K`-conjugate into `E`
  have hconjE : ∀ x : K, orderOf x = 2 → ∃ g : K, g * x * g⁻¹ ∈ E := by
    intro x hx
    have hx2 : x ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
    have hxp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hx]
      norm_num
    obtain ⟨P, hPle⟩ := hxp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P S'
    have hmem : g * x * g⁻¹ ∈ (S' : Subgroup K) := by
      have h1 : MulAut.conj g • x ∈ MulAut.conj g • (P : Subgroup K) :=
        Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P : Subgroup K)
          (hPle (Subgroup.mem_zpowers x))
      have h2 : MulAut.conj g • (P : Subgroup K) = (S' : Subgroup K) := by
        rw [← Sylow.coe_subgroup_smul]
        exact congrArg (fun T : Sylow 2 K => (T : Subgroup K)) hg
      rw [h2] at h1
      simpa [MulAut.conj_apply] using h1
    refine ⟨g, mem_of_mem_sup_of_sq_eq_one E C hC hZodd hCodd (hS'le hmem) ?_⟩
    rw [show g * x * g⁻¹ = (MulAut.conj g) x by rw [MulAut.conj_apply], ← map_pow, hx2,
      map_one]
  -- all involutions of `K` are `K`-conjugate
  intro x hx y hy
  simp only [Work.GW2.involutionSet, Set.mem_ofPred_eq, Subgroup.mem_top, true_and] at hx hy
  obtain ⟨g, hg⟩ := hconjE x hx
  obtain ⟨h, hh⟩ := hconjE y hy
  have hx2 : x ^ 2 = 1 := by have h := pow_orderOf_eq_one x; rwa [hx] at h
  have hy2 : y ^ 2 = 1 := by have h := pow_orderOf_eq_one y; rwa [hy] at h
  have hgs : orderOf (g * x * g⁻¹) = 2 := by
    rw [orderOf_eq_prime_iff]
    refine ⟨by rw [show g * x * g⁻¹ = (MulAut.conj g) x by rw [MulAut.conj_apply], ← map_pow,
      hx2, map_one], ?_⟩
    intro h1
    have hxne : x ≠ 1 := by
      intro hx1
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    exact hxne (by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group)
  have hhs : orderOf (h * y * h⁻¹) = 2 := by
    rw [orderOf_eq_prime_iff]
    refine ⟨by rw [show h * y * h⁻¹ = (MulAut.conj h) y by rw [MulAut.conj_apply], ← map_pow,
      hy2, map_one], ?_⟩
    intro h1
    have hyne : y ≠ 1 := by
      intro hy1
      rw [hy1, orderOf_one] at hy
      exact absurd hy (by norm_num)
    exact hyne (by
      calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
        _ = h⁻¹ * 1 * h := by rw [h1]
        _ = 1 := by group)
  obtain ⟨e, heE, hee⟩ := hE1 (g * x * g⁻¹) hg (h * y * h⁻¹) hh hgs hhs
  refine ⟨h⁻¹ * e * g, trivial, ?_⟩
  calc (h⁻¹ * e * g) * x * (h⁻¹ * e * g)⁻¹
      = h⁻¹ * (e * (g * x * g⁻¹) * e⁻¹) * h := by group
    _ = h⁻¹ * (h * y * h⁻¹) * h := by rw [hee]
    _ = y := by group

end Work.CORE2A
