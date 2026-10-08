/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4)

# AREA CORE4 — Bender §4, the identity `|C_E(t)| = 2 |K| |S₀|`

Bender 1981, §4, p. 227: after writing `k` (even) and `k'` (odd) for the two halves `(q ∓ 1)/2`
of `|C_E(t)| = 2k`, he proves `S ≤ E` and concludes

  `k = |K| · |S₀|`,   i.e.   `|C_E(t)| = 2 |K| |S₀|`,

where `E = E(M) ≅ L₂(q)`, `t` is the involution of `S₀`, `K = I_{U∩M}(s)` and `s ∈ S ∖ S₀`.

The content formalised here is a general consequence of the §4 data (1)–(6) together with
`E ≅ L₂(q)` and `S ≤ E`:

* `H = U · S` with `U = O(H)` of odd order, so the quotient `H/U ≅ S` is a 2-group and every
  odd-order element of `H` lies in `U`;
* every element of `C_E(t) = E ⊓ H` centralises `t`, so `U ⊓ E` is exactly the odd part of the
  dihedral group `C_E(t)`, and `C_E(t) = (U ⊓ E) · S` with `(U ⊓ E) ⊓ S = 1`;
* `K ⊆ E`: `s ∈ E = E(M) ⊴ M` inverts `k ∈ K`, so `k² = (k s k⁻¹) s⁻¹ ∈ E`, and `k` has odd
  order, whence `k = (k²)^{orderOf k + 1}/2 ∈ E`;
* `U ⊓ E ⊆ K`: `K ≠ 1`; if `s` centralised `U ⊓ E`, then `s = t` would give
  `K ≤ U ⊓ E ⊆ C(s) = B₀`, i.e. `K = K ⊓ B₀ = 1`.  So `s` acts nontrivially on the odd part of
  the dihedral `C_E(t) ≅ DihedralGroup k`, and as `s ∉ S₀` is not the central involution it
  inverts every element of odd order.

Hence `U ⊓ E = K` and `|C_E(t)| = |U ⊓ E| · |S| = |K| · 2 |S₀|`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2CHs
import Submission.Work.CORE4.Case2Parity
import Submission.Work.CORE4.Case2RelIndexMH
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.Dihedral.Defs

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

set_option linter.style.haveILetI false

/-! ## Elementary transport lemmas -/

section Transport

variable {G₀ H₀ : Type*} [Group G₀] [Group H₀]

/-- A group isomorphism maps the centralizer of `z` into the centralizer of `ψ z`. -/
theorem map_mem_centralizer_singleton (ψ : G₀ ≃* H₀) {z x : G₀}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G₀)) :
    ψ x ∈ Subgroup.centralizer ({ψ z} : Set H₀) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  simpa [map_mul] using congrArg ψ hx

/-- An isomorphism of groups restricts to an isomorphism of the centralizers of `z` and `ψ z`. -/
noncomputable def centralizerSingletonMulEquiv (ψ : G₀ ≃* H₀) (z : G₀) :
    ↥(Subgroup.centralizer ({z} : Set G₀)) ≃* ↥(Subgroup.centralizer ({ψ z} : Set H₀)) :=
  { toFun := fun x => ⟨ψ x.1, map_mem_centralizer_singleton ψ x.2⟩
    invFun := fun y => ⟨ψ.symm y.1, by
      have h1 := map_mem_centralizer_singleton ψ.symm y.2
      simpa using h1⟩
    left_inv := fun x => Subtype.ext (by simp)
    right_inv := fun y => Subtype.ext (by simp)
    map_mul' := fun x y => Subtype.ext (by simp [map_mul]) }

end Transport

section TransportSub

variable {G : Type*} [Group G] {E : Subgroup G}

/-- Membership in the centralizer of `z` computed inside `E` upgrades to the ambient group. -/
theorem mem_centralizer_coe {z x : G} (hz : z ∈ E) (hx : x ∈ E)
    (h : (⟨x, hx⟩ : ↥E) ∈ Subgroup.centralizer ({⟨z, hz⟩} : Set ↥E)) :
    x ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  exact congrArg Subtype.val h

/-- The same statement in the opposite direction. -/
theorem mem_centralizer_subtype {z x : G} (hz : z ∈ E) (hx : x ∈ E)
    (h : x ∈ Subgroup.centralizer ({z} : Set G)) :
    (⟨x, hx⟩ : ↥E) ∈ Subgroup.centralizer ({⟨z, hz⟩} : Set ↥E) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  exact Subtype.ext h

end TransportSub

/-! ## The dihedral group: odd-order elements lie in the rotation subgroup -/

/-- An element of `DihedralGroup n` of odd order lies in the rotation subgroup
`Work.Dihedral.rot n` (every element outside it is an involution `sr i`). -/
theorem odd_orderOf_mem_rot {n : ℕ} {x : DihedralGroup n} (h : Odd (orderOf x)) :
    x ∈ Work.Dihedral.rot n := by
  by_contra hx
  obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hx
  have h2 : orderOf (DihedralGroup.sr i) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two, DihedralGroup.sr_mul_sr, sub_self,
      DihedralGroup.r_zero]
  have h1 : orderOf (DihedralGroup.sr i) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
    · exact h'
    · rw [h'] at h
      exact absurd h (by decide)
  rw [orderOf_eq_one_iff] at h1
  exact hx (h1.symm ▸ Subgroup.one_mem _)

/-! ## The two structural facts about `K` -/

section Structural

variable {G : Type} [Group G] [Finite G]
variable {B : Work.GW2.BenderSetup G} {h : Work.GW2.Case2Ctx B}

/-- `S ≤ E(M)` (§4 (9)). -/
theorem S_le_layerIn (h : Work.GW2.Case2Ctx B) :
    (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M := by
  obtain ⟨p, m, hp, hpodd, h7, ⟨φ⟩, hSE⟩ := h.nine
  exact hSE

/-- **§4, `K ⊆ E(M)`.**  `s ∈ E = E(M) ⊴ M` inverts every `k ∈ K`; hence
`k² = (k s k⁻¹) s⁻¹ ∈ E`, and as `k` has odd order (`K ≤ U`, `U` odd),
`k = (k²)^{orderOf k + 1}/2 ∈ E`. -/
theorem K_le_layerIn (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    h.D.K ≤ Work.GW2.layerIn h.D.M := by
  intro k hk
  have hkM : k ∈ h.D.M := h.D.K_le_M B hk
  have hsE : h.D.s ∈ Work.GW2.layerIn h.D.M := h.D.s_mem.2
  have hkinv : h.D.s * k * h.D.s⁻¹ = k⁻¹ := h.D.K_inv B k hk
  have hn : ((Work.GW2.layerIn h.D.M).subgroupOf h.D.M).Normal :=
    Work.GW2.Case2Ctx.layerIn_subgroupOf_normal h
  have hconj : k * h.D.s * k⁻¹ ∈ Work.GW2.layerIn h.D.M :=
    (Subgroup.normal_subgroupOf_iff (Work.CORE4.layerIn_le h.D.M)).mp hn h.D.s k hsE hkM
  have hk2 : k ^ 2 ∈ Work.GW2.layerIn h.D.M := by
    have h1 : h.D.s * k⁻¹ * h.D.s⁻¹ = k := by
      have h3 := congrArg (fun z : G => z⁻¹) hkinv
      rw [mul_inv_rev, mul_inv_rev, inv_inv] at h3
      simpa [mul_assoc] using h3
    have heq : (k * h.D.s * k⁻¹) * h.D.s⁻¹ = k * k := by
      calc (k * h.D.s * k⁻¹) * h.D.s⁻¹
          = k * (h.D.s * k⁻¹ * h.D.s⁻¹) := by group
        _ = k * k := by rw [h1]
    have heq2 : k ^ 2 = (k * h.D.s * k⁻¹) * h.D.s⁻¹ := by
      rw [pow_two]
      exact heq.symm
    rw [heq2]
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hsE)
  have hkodd : Odd (orderOf k) :=
    Odd.of_dvd_nat B.U_odd
      ((Subgroup.orderOf_dvd_natCard h.D.K hk).trans (Subgroup.card_dvd_of_le (h.D.K_le_U B)))
  obtain ⟨j, hj⟩ := hkodd
  have hpow : (k ^ 2) ^ (j + 1) = k := by
    rw [← pow_mul]
    have h2 : 2 * (j + 1) = orderOf k + 1 := by rw [hj]; ring
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  exact hpow ▸ Subgroup.pow_mem _ hk2 (j + 1)

/-- **Bender (1), (5) and (9): `U ⊓ E(M) ⊆ K`.**  `K ≠ 1`; if `s` centralised `U ⊓ E` then
`s = t` would force `K ≤ U ⊓ E ⊆ C(s) = B₀`, i.e. `K = K ⊓ B₀ = 1`.  So `s` acts nontrivially on
the odd part of the dihedral group `C_E(t) ≅ DihedralGroup k`; as `s ∈ S ∖ S₀` is not the central
involution, it inverts every element of odd order. -/
theorem U_inf_layerIn_le_K (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    B.U ⊓ Work.GW2.layerIn h.D.M ≤ h.D.K := by
  classical
  obtain ⟨p, m, hp, hpodd, h7, ⟨φ⟩, hSE⟩ := h.nine
  haveI := hp
  have htE : B.t ∈ Work.GW2.layerIn h.D.M := h.D.t_mem
  have htE2 : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn h.D.M)) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have ht' : orderOf (φ ⟨B.t, htE⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact htE2
  obtain ⟨n, _hn, ⟨ψ⟩⟩ :=
    I.toolkit.l2cent p m hpodd (by omega : 5 ≤ p ^ m) (φ ⟨B.t, htE⟩) ht'
  -- The isomorphism `Ψ : ↥(E ⊓ H) ≃* DihedralGroup n` (`E = E(M)`, `H = C_G(t)`).
  let Ψ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H) ≃* DihedralGroup n :=
    (((Subgroup.subgroupOfEquivOfLe (inf_le_left : Work.GW2.layerIn h.D.M ⊓ B.H ≤
        Work.GW2.layerIn h.D.M)).symm.trans
      (MulEquiv.subgroupCongr (subgroupOf_inf_centralizer (Work.GW2.layerIn h.D.M) B.t htE))).trans
      (centralizerSingletonMulEquiv (φ : ↥(Work.GW2.layerIn h.D.M) ≃* PSL(2, GaloisField p m))
        ⟨B.t, htE⟩)).trans ψ
  have hsD : h.D.s ∈ Work.GW2.layerIn h.D.M ⊓ B.H :=
    ⟨h.D.s_mem.2, B.S_le_H h.D.s_mem.1⟩
  -- every element of `U ⊓ E` maps into the rotation subgroup
  have hrot : ∀ (y : G) (hy : y ∈ B.U ⊓ Work.GW2.layerIn h.D.M),
      Ψ ⟨y, ⟨hy.2, B.U_le_H hy.1⟩⟩ ∈ Work.Dihedral.rot n := by
    intro y hy
    refine odd_orderOf_mem_rot ?_
    rw [MulEquiv.orderOf_eq]
    simpa only [← Subgroup.orderOf_coe] using
      Odd.of_dvd_nat B.U_odd (Subgroup.orderOf_dvd_natCard B.U hy.1)
  intro x hx
  obtain ⟨hxU, hxE⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ B.H := B.U_le_H hxU
  have hxD : x ∈ Work.GW2.layerIn h.D.M ⊓ B.H := ⟨hxE, hxH⟩
  obtain ⟨j, hj⟩ := Work.Dihedral.mem_rot.mp (hrot x hx)
  rcases Work.Dihedral.eq_r_or_sr (Ψ ⟨h.D.s, hsD⟩) with ⟨i, hi⟩ | ⟨i, hi⟩
  · -- `Ψ s = r i`: `s` centralises `U ⊓ E`, so `K ≤ U ⊓ E ≤ C(s) = B₀` and `K = 1`.
    exfalso
    have hcentral : ∀ y ∈ (B.U ⊓ Work.GW2.layerIn h.D.M), h.D.s * y * h.D.s⁻¹ = y := by
      intro y hy
      obtain ⟨hyU, hyE⟩ := Subgroup.mem_inf.mp hy
      have hyH : y ∈ B.H := B.U_le_H hyU
      have hyD : y ∈ Work.GW2.layerIn h.D.M ⊓ B.H := ⟨hyE, hyH⟩
      obtain ⟨j', hj'⟩ := Work.Dihedral.mem_rot.mp (hrot y hy)
      have hmem : h.D.s * y * h.D.s⁻¹ ∈ Work.GW2.layerIn h.D.M ⊓ B.H :=
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ h.D.s_mem.2 hyE)
            (Subgroup.inv_mem _ h.D.s_mem.2),
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (B.S_le_H h.D.s_mem.1) hyH)
            (Subgroup.inv_mem _ (B.S_le_H h.D.s_mem.1))⟩
      have hcomp : (⟨h.D.s * y * h.D.s⁻¹, hmem⟩ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H)) =
          ⟨h.D.s, hsD⟩ * ⟨y, hyD⟩ * ⟨h.D.s, hsD⟩⁻¹ := by
        ext
        simp
      have h2 : (⟨h.D.s * y * h.D.s⁻¹, hmem⟩ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H)) =
          ⟨y, hyD⟩ := by
        apply Ψ.injective
        rw [hcomp, map_mul, map_mul, map_inv, hi, hj']
        rw [DihedralGroup.r_mul_r, DihedralGroup.inv_r, DihedralGroup.r_mul_r]
        congr 1
        ring
      exact congrArg Subtype.val h2
    -- `K ≤ B₀ = C_{U∩M}(s)`
    have hKleB0 : h.D.K ≤ h.D.B0 := by
      intro k hk
      have hkU : k ∈ B.U := h.D.K_le_U B hk
      have hkE : k ∈ Work.GW2.layerIn h.D.M := K_le_layerIn B h hk
      have hkR : k ∈ B.U ⊓ Work.GW2.layerIn h.D.M := ⟨hkU, hkE⟩
      rw [Work.GW2.Case2Pre.B0_eq B h.D h.pre]
      refine Subgroup.mem_inf.mpr ⟨hkU, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : k * h.D.s = h.D.s * k := by
        have h4 : h.D.s * k = k * h.D.s := by
          calc h.D.s * k = (h.D.s * k * h.D.s⁻¹) * h.D.s := by group
            _ = k * h.D.s := by rw [hcentral k hkR]
        exact h4.symm
      exact h1
    have hKbot : h.D.K = ⊥ := by
      have h1 : h.D.K ≤ h.D.K ⊓ h.D.B0 := le_inf le_rfl hKleB0
      rw [Case2KB0_inf B h, le_bot_iff] at h1
      exact h1
    exact Case2K1_ne_bot I hbc h (by simp [hKbot])
  · -- `Ψ s = sr i`: `s` inverts every element of `U ⊓ E`.
    have hmem : h.D.s * x * h.D.s⁻¹ ∈ Work.GW2.layerIn h.D.M ⊓ B.H :=
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ h.D.s_mem.2 hxE) (Subgroup.inv_mem _ h.D.s_mem.2),
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (B.S_le_H h.D.s_mem.1) hxH)
          (Subgroup.inv_mem _ (B.S_le_H h.D.s_mem.1))⟩
    have hcomp : (⟨h.D.s * x * h.D.s⁻¹, hmem⟩ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H)) =
        ⟨h.D.s, hsD⟩ * ⟨x, hxD⟩ * ⟨h.D.s, hsD⟩⁻¹ := by
      ext
      simp
    have h2 : (⟨h.D.s * x * h.D.s⁻¹, hmem⟩ : ↥(Work.GW2.layerIn h.D.M ⊓ B.H)) =
        ⟨x, hxD⟩⁻¹ := by
      apply Ψ.injective
      rw [hcomp, map_mul, map_mul, map_inv, hi, hj, map_inv, hj]
      rw [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
      congr 1
      ring
    have hxinv : h.D.s * x * h.D.s⁻¹ = x⁻¹ := by
      simpa using congrArg Subtype.val h2
    exact (Set.ext_iff.mp h.D.K_def x).mpr
      ⟨Subgroup.mem_inf.mpr ⟨hxU, Work.CORE4.layerIn_le h.D.M hxE⟩, hxinv⟩

end Structural

/-! ## The decomposition `E ⊓ H = (U ⊓ E) · S` -/

section Decomposition

variable {G : Type} [Group G] [Finite G]
variable {B : Work.GW2.BenderSetup G} {h : Work.GW2.Case2Ctx B}

/-- `E(M) ⊓ C_G(t) = (U ⊓ E(M)) · S`: since `H = U · S` and `U ⊓ S = 1`, every element of
`E ⊓ H` is the product of an element of `U ⊓ E` and one of `S`. -/
theorem layerIn_inter_H_eq (I : Work.GW2.C4Inputs) (h : Work.GW2.Case2Ctx B) :
    Work.GW2.layerIn h.D.M ⊓ B.H =
      (B.U ⊓ Work.GW2.layerIn h.D.M) ⊔ (B.S : Subgroup G) := by
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M := S_le_layerIn h
  have hH : B.H = B.U ⊔ (B.S : Subgroup G) := Work.GW2.Case2Ctx.H_eq_U_sup_S I h
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxE, hxH⟩ := Subgroup.mem_inf.mp hx
    have hxH' : (⟨x, hxH⟩ : ↥B.H) ∈
        (B.U.subgroupOf B.H) ⊔ ((B.S : Subgroup G).subgroupOf B.H) := by
      rw [← Subgroup.subgroupOf_sup B.U_le_H B.S_le_H, ← hH, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    haveI : (B.U.subgroupOf B.H).Normal := B.U_normal
    obtain ⟨u, hu, s, hs, hus⟩ := Subgroup.mem_sup_of_normal_left.mp hxH'
    have huU : (u : G) ∈ B.U := Subgroup.mem_subgroupOf.mp hu
    have hsS : (s : G) ∈ (B.S : Subgroup G) := Subgroup.mem_subgroupOf.mp hs
    have hxs : (u : G) * (s : G) = x := congrArg Subtype.val hus
    have huE : (u : G) ∈ Work.GW2.layerIn h.D.M := by
      have h2 : (u : G) = x * (s : G)⁻¹ := by rw [← hxs]; group
      rw [h2]
      exact Subgroup.mul_mem _ hxE (Subgroup.inv_mem _ (hSE hsS))
    rw [← hxs]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨huU, huE⟩) hsS
  · refine sup_le ?_ ?_
    · exact le_inf inf_le_right (le_trans inf_le_left B.U_le_H)
    · exact le_inf hSE B.S_le_H

end Decomposition

/-! ## Bender §4, p. 227: `|C_E(t)| = 2 |K| |S₀|` -/

/-- **Bender 1981, §4, p. 227.**  In the §4 configuration with `E = E(M) ≅ L₂(q)`, the involution
centralizer `C_E(t) = E ⊓ C_G(t)` has order `2 |K| |S₀|` — Bender's `k = |K| · |S₀|`. -/
theorem Case2EHcard :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) =
          2 * (Nat.card ↥h.D.K * Nat.card ↥B.S0) := by
  intro G _ _ I hbc B h
  -- `U ⊓ E = K`
  have hUKE : B.U ⊓ Work.GW2.layerIn h.D.M = h.D.K :=
    le_antisymm (U_inf_layerIn_le_K I hbc B h)
      (le_inf (h.D.K_le_U B) (K_le_layerIn B h))
  -- `(U ⊓ E) ⊓ S = 1`
  have hsup : (B.U ⊓ Work.GW2.layerIn h.D.M) ⊓ (B.S : Subgroup G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_bot.mp (B.U_inf_S ▸ Subgroup.mem_inf.mpr ⟨hy1.1, hy2⟩)
  -- `S` normalises `U ⊓ E`
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn h.D.M := S_le_layerIn h
  have hnorm : (B.S : Subgroup G) ≤
      Subgroup.normalizer ((B.U ⊓ Work.GW2.layerIn h.D.M : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨hyU, hyE⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y x hyU (B.S_le_H hx),
       (Subgroup.normal_subgroupOf_iff (Work.CORE4.layerIn_le h.D.M)).mp
         (Work.GW2.Case2Ctx.layerIn_subgroupOf_normal h) y x hyE
         (Work.CORE4.layerIn_le h.D.M (hSE hx))⟩
  -- `|S| = 2 |S₀|`
  have hcardS : Nat.card ↥(B.S : Subgroup G) = 2 * Nat.card ↥B.S0 := by
    have hh := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [inf_eq_left.mpr B.S0_le, B.S0_index] at hh
    exact hh.symm
  rw [layerIn_inter_H_eq I h,
    Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hnorm hsup, hUKE, hcardS]
  ring

end Work.CORE4
