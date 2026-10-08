/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# CORE2A: the involutions of `H` other than `t` lie in `I_U(s) · (S − S₀)`

Bender 1981 §3 counts the involutions of `H = C_G(t)`.  Their number is `3 + 2·|I_U(s)|`:
the four-group `O₂(Ĥ) ⊔ ⟨t⟩` contributes `3`, and the `n = |S : S₀|` cosets of `S₀` in `S`
contribute `|I_U(s)|` involutions `u·(s·c)` each.

This file proves the underlying *surjectivity* statement: with `H = U ⊔ S` (`T.split`) an
involution `h ∈ H`, `h ≠ t` is always of the shape `u·(s·c)` with `c ∈ S₀` and
`u ∈ I_U(s) = {u ∈ U | s·u·s⁻¹ = u⁻¹}` (here `I_U(s)` is `invSet B.U s`).

The argument is elementary.  Write `h = u·y` with `u ∈ U`, `y ∈ S`.
* If `y ∈ S₀`, then `y` commutes with `u` (`hS0C`), so `1 = h² = u²·y²` gives
  `u² = y⁻² ∈ U ⊓ S₀ = 1`; as `U` has odd order, `u = 1`, and `h = y` is the unique involution
  `t` of the cyclic group `S₀` — contradicting `h ≠ t`.
* Hence `y ∉ S₀`, so `y = s·c` with `c ∈ S₀` (`S₀` has index two in `S`).  From
  `1 = h² = (u·y)²` we get `u·y·u = y⁻¹`, and multiplying by `y⁻¹` gives
  `u·(y·u·y⁻¹) = y⁻² ∈ U ⊓ S₀ = 1`; therefore `y·u·y⁻¹ = u⁻¹`, and since `c` centralizes `u`,
  `s·u·s⁻¹ = y·u·y⁻¹ = u⁻¹`, i.e. `u ∈ I_U(s)`.
-/

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 1. Two elementary subgroup lemmas -/

section Aux

variable {G : Type} [Group G] [Finite G]

/-- `O(K)`, transported into the ambient group, is a normal subgroup of `K`
(`(oddCoreIn K).subgroupOf K = oddCore ↥K`). -/
theorem subgroupOf_oddCoreIn_normal (K : Subgroup G) : ((oddCoreIn K).subgroupOf K).Normal := by
  have hinj : Function.Injective (fun L : Subgroup ↥K => L.map K.subtype) :=
    Subgroup.map_injective (f := K.subtype) Subtype.val_injective
  have heq : (oddCoreIn K).subgroupOf K = oddCore ↥K := by
    apply hinj
    calc ((oddCoreIn K).subgroupOf K).map K.subtype
        = oddCoreIn K ⊓ K := Subgroup.subgroupOf_map_subtype _ _
      _ = oddCoreIn K := inf_eq_left.mpr (Subgroup.map_subtype_le (oddCore ↥K))
      _ = (oddCore ↥K).map K.subtype := rfl
  rw [heq]
  infer_instance

/-- If `K = A ⊔ B` with `A ◁ K`, then every element of `K` is a product `a * b`
with `a ∈ A`, `b ∈ B`. -/
theorem mem_sup_decomposition {A B K : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K)
    (hAnorm : (A.subgroupOf K).Normal) (hsup : A ⊔ B = K) :
    ∀ x ∈ K, ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  intro x hx
  have hsup' : A.subgroupOf K ⊔ B.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAK hBK, hsup, Subgroup.subgroupOf_self]
  have hmem : (⟨x, hx⟩ : ↥K) ∈ A.subgroupOf K ⊔ B.subgroupOf K := by
    rw [hsup']
    trivial
  haveI := hAnorm
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨(a : G), ha, (b : G), hb, ?_⟩
  have := congrArg (fun z : ↥K => (z : G)) hab
  simpa using this

/-- If `S₀` has index two in `S`, then two elements of `S` outside `S₀` differ by an element of
`S₀`: `y = s * c` with `c ∈ S₀`. -/
theorem exists_mul_of_notMem_relIndex_two {S S0 : Subgroup G} (hidx : S0.relIndex S = 2)
    {s y : G} (hs : s ∈ S) (hs0 : s ∉ S0) (hy : y ∈ S) (hy0 : y ∉ S0) :
    ∃ c ∈ S0, y = s * c := by
  have hidx' : (S0.subgroupOf S).index = 2 := hidx
  have hmem : (⟨s⁻¹, S.inv_mem hs⟩ : ↥S) * ⟨y, hy⟩ ∈ S0.subgroupOf S := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx']
    exact ⟨fun h => absurd (inv_mem_iff.mp h) hs0, fun h => absurd h hy0⟩
  have hc : s⁻¹ * y ∈ S0 := Subgroup.mem_subgroupOf.mp hmem
  exact ⟨s⁻¹ * y, hc, by rw [mul_inv_cancel_left]⟩

end Aux

/-! ## 2. The surjectivity statement -/

theorem exists_mul_of_mem_involutionSet_H (T : Work.GW2.LocalToolkit) {G : Type} [Group G]
    [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (n : ℕ) (hn : 2 ≤ n)
    (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n))
    {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0)
    (hS0C : B.S0 ≤ Subgroup.centralizer (B.U : Set G))
    {h : G} (hh : h ∈ Work.GW2.involutionSet B.H) (hne : h ≠ B.t) :
    ∃ c ∈ B.S0, ∃ u ∈ Work.GW2.invSet B.U s, u * (s * c) = h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Bender p. 219: `H = U ⊔ S` (`T.split`), with `U = O(H)`.
  have hUS : B.U ⊔ (B.S : Subgroup G) = B.H :=
    T.split G B.S n hn hdih B.t (bSetup_t_mem_S B) B.t_order fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hx) B.t (by simp)).symm
  -- `U ◁ H`, hence `H ≤ N_G(U)`; and `U` has odd order.
  have hUnorm : (B.U.subgroupOf B.H).Normal := subgroupOf_oddCoreIn_normal B.H
  have hHN : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (bSetup_U_le_H B)).mp hUnorm
  have hUodd : Odd (Nat.card B.U) := bSetup_U_odd B
  -- `U ⊓ S₀ = 1` (coprime orders).
  have hUS0 : B.U ⊓ B.S0 = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (B.S.isPGroup'.to_le B.S0_le)
    rw [hk]
    exact (hUodd.coprime_two_right).pow_right k
  -- Decompose `h = u * y` with `u ∈ U`, `y ∈ S`.
  obtain ⟨u, hu, y, hy, huy⟩ :=
    mem_sup_decomposition (A := B.U) (B := B.S) (K := B.H) (bSetup_U_le_H B) (bSetup_S_le_H B)
      hUnorm hUS h hh.1
  -- `h` is an involution.
  have hh2 : h * h = 1 := by
    have h2 : h ^ 2 = 1 := by rw [← hh.2]; exact pow_orderOf_eq_one h
    simpa [pow_two] using h2
  by_cases hy0 : y ∈ B.S0
  · -- Case `y ∈ S₀`: then `u = 1` and `h = y = t`, contradicting `h ≠ t`.
    have hcent : u * y = y * u := Subgroup.mem_centralizer_iff.mp (hS0C hy0) u hu
    have hmul : (u * y) * (u * y) = u ^ 2 * y ^ 2 := by
      calc (u * y) * (u * y) = u * (y * u) * y := by group
        _ = u * (u * y) * y := by rw [← hcent]
        _ = u ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group
    have hsq : u ^ 2 * y ^ 2 = 1 := by
      rw [← hmul, huy]; exact hh2
    have hmem : u ^ 2 ∈ B.U ⊓ B.S0 :=
      ⟨B.U.pow_mem hu 2, by
        rw [eq_inv_of_mul_eq_one_left hsq]
        exact B.S0.inv_mem (B.S0.pow_mem hy0 2)⟩
    have hu2 : u ^ 2 = 1 := by simpa [hUS0] using hmem
    have hu1 : u = 1 := by
      have hdvd2 : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
      have hdvdU : orderOf u ∣ Nat.card B.U := Subgroup.orderOf_dvd_natCard B.U hu
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        rw [h] at hdvdU
        exact (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr hdvdU)
    have hyh : y = h := by rw [← huy, hu1, one_mul]
    have hyt : y = B.t := by
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      have h1 : (⟨y, hy0⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ :=
        eq_of_orderOf_eq_two_of_isCyclic (a := (⟨y, hy0⟩ : ↥B.S0)) (b := ⟨B.t, B.t_mem⟩)
          (by rw [Subgroup.orderOf_mk, hyh]; exact hh.2)
          (by rw [Subgroup.orderOf_mk]; exact B.t_order)
      exact congrArg Subtype.val h1
    exact absurd (hyh ▸ hyt) hne
  · -- Case `y ∉ S₀`: `y = s * c`, and involutivity of `h` forces `s * u * s⁻¹ = u⁻¹`.
    obtain ⟨c, hc, hyc⟩ :=
      exists_mul_of_notMem_relIndex_two (S := (B.S : Subgroup G)) (S0 := B.S0) B.S0_index
        hsS hs0 hy hy0
    -- `y ^ 2 ∈ S₀` because `S₀` has index two in `S`.
    have hy2 : y ^ 2 ∈ B.S0 := by
      have hidx' : (B.S0.subgroupOf (B.S : Subgroup G)).index = 2 := B.S0_index
      have h := Subgroup.sq_mem_of_index_two hidx' (⟨y, hy⟩ : ↥(B.S : Subgroup G))
      exact Subgroup.mem_subgroupOf.mp h
    -- `y` normalizes `U` (as an element of `S ≤ H`).
    have hyuy : y * u * y⁻¹ ∈ B.U :=
      (Subgroup.mem_normalizer_iff.mp (hHN (bSetup_S_le_H B hy)) u).mp hu
    -- The key computation: `u * y * u = y⁻¹`, hence `u * (y * u * y⁻¹) = y⁻²`.
    have hUU : u * (y * u * y⁻¹) = (y ^ 2)⁻¹ := by
      have h1 : (u * y * u) * y = 1 := by
        have h2 := hh2
        rw [← huy] at h2
        calc (u * y * u) * y = (u * y) * (u * y) := by group
          _ = 1 := h2
      have h2 : u * y * u = y⁻¹ := by
        calc u * y * u = (u * y * u) * 1 := (mul_one _).symm
          _ = (u * y * u) * (y * y⁻¹) := by rw [mul_inv_cancel]
          _ = ((u * y * u) * y) * y⁻¹ := by group
          _ = 1 * y⁻¹ := by rw [h1]
          _ = y⁻¹ := one_mul _
      calc u * (y * u * y⁻¹) = (u * y * u) * y⁻¹ := by group
        _ = y⁻¹ * y⁻¹ := by rw [h2]
        _ = (y ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
    -- Hence `y * u * y⁻¹ = u⁻¹`, since `U ⊓ S₀ = 1`.
    have hyuy1 : y * u * y⁻¹ = u⁻¹ := by
      have hmem : u * (y * u * y⁻¹) ∈ B.U ⊓ B.S0 :=
        ⟨B.U.mul_mem hu hyuy, by rw [hUU]; exact B.S0.inv_mem hy2⟩
      have h1 : u * (y * u * y⁻¹) = 1 := by simpa [hUS0] using hmem
      calc y * u * y⁻¹ = 1 * (y * u * y⁻¹) := (one_mul _).symm
        _ = (u⁻¹ * u) * (y * u * y⁻¹) := by rw [inv_mul_cancel]
        _ = u⁻¹ * (u * (y * u * y⁻¹)) := by group
        _ = u⁻¹ * 1 := by rw [h1]
        _ = u⁻¹ := mul_one _
    -- `c ∈ S₀` centralizes `U`, so `s * u * s⁻¹ = (s * c) * u * (s * c)⁻¹ = u⁻¹`.
    have hcu : c * u * c⁻¹ = u := by
      rw [← Subgroup.mem_centralizer_iff.mp (hS0C hc) u hu, mul_inv_cancel_right]
    have hsu : s * u * s⁻¹ = u⁻¹ := by
      have hstep : (s * c) * u * (s * c)⁻¹ = s * u * s⁻¹ := by
        calc (s * c) * u * (s * c)⁻¹ = s * (c * u * c⁻¹) * s⁻¹ := by rw [mul_inv_rev]; group
          _ = s * u * s⁻¹ := by rw [hcu]
      calc s * u * s⁻¹ = (s * c) * u * (s * c)⁻¹ := hstep.symm
        _ = u⁻¹ := by rw [← hyc]; exact hyuy1
    exact ⟨c, hc, u, ⟨hu, hsu⟩, by rw [← hyc]; exact huy⟩

end Work.CORE2A
