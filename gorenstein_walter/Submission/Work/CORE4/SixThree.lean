/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# Bender 1981, §4 (3): `F(U) ∩ M = K₁ F`

This is Bender's display (3) of §4 (p. 224 of Bender, *Finite groups with dihedral Sylow
2-subgroups*, J. Algebra **70** (1981) 216–228):

> `F := B ∩ F(U) = C_{F(U)}(s)` and `F(U) ∩ M = K₁ F`, `K₁ := F(U) ∩ K`.

In our vocabulary this reads

  `Work.GW2.fittingIn B.U ⊓ D.M = (Work.GW2.fittingIn B.U ⊓ D.K) ⊔ D.F`.

The statement is *not* a formal consequence of the subgroup-level data of `Case2Pre`/`Case2Data`
alone (the modular identity fails in the abstract subgroup lattice; see the discussion in
`CORE4/Case2Six.lean`).  What makes it true is the ambient structure of `BenderSetup`, which the
hypothesis list does carry and which Bender uses silently: `S ≤ C_G(t) = B.H` (`S_le_H`), so that
`s ∈ S ≤ H`, `U = O(H) ⊴ H`, and the Fitting subgroup `F(U)`, being characteristic in `U`, is
invariant under conjugation by `s`.  With `A := F(U)` thus `s`-invariant, every `x ∈ A ⊓ M` can be
written `x = k b` (because `K ⊴ U ⊓ M = K ⊔ B₀`, a consequence of Bender's 1.5(iii) as packaged in
`LocalToolkit.c15`), and then `k² = x · (s x⁻¹ s⁻¹) ∈ A`; since `k ∈ K ≤ U` has odd order,
`k ∈ A`, whence `b = k⁻¹ x ∈ A` and `x = k b ∈ (A ⊓ K)(A ⊓ B₀) = (A ⊓ K) ⊔ F`.

## Contents

* `exists_mul_of_mem_of_normal_subgroupOf` — if `K ⊴ X` inside `X` and `K ⊔ B₀ = X`, then every
  element of `X` is of the form `k * b` with `k ∈ K`, `b ∈ B₀`;
* `conjSub_fittingIn` — conjugation by `g` commutes with `F(·)`, i.e.
  `conjSub g (F(U)) = F(conjSub g U)`;
* `SixThree` — the target statement.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.FittingInConj

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

/-- **The normal product.**  If `K` is normal in `X` (as `(K.subgroupOf X).Normal`), `B₀ ≤ X`
and `K ⊔ B₀ = X`, then `X = K · B₀`: every element of `X` is a product `k * b` with `k ∈ K`,
`b ∈ B₀`. -/
theorem exists_mul_of_mem_of_normal_subgroupOf {G : Type*} [Group G] {X K B0 : Subgroup G}
    (hK : K ≤ X) (hB0 : B0 ≤ X) (hnorm : (K.subgroupOf X).Normal) (hsup : K ⊔ B0 = X) :
    ∀ x ∈ X, ∃ k ∈ K, ∃ b ∈ B0, k * b = x := by
  intro x hx
  have hsup' : (K.subgroupOf X) ⊔ (B0.subgroupOf X) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK hB0, hsup, Subgroup.subgroupOf_self]
  have hx' : (⟨x, hx⟩ : ↥X) ∈ (K.subgroupOf X) ⊔ (B0.subgroupOf X) := by
    rw [hsup']; exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := K.subgroupOf X) (t := B0.subgroupOf X)
      (hs := hnorm)).mp hx'
  exact ⟨y.1, Subgroup.mem_subgroupOf.mp hy, z.1, Subgroup.mem_subgroupOf.mp hz,
    by have h := congrArg Subtype.val hyz; simpa using h⟩

/-- **`F` commutes with conjugation.**  `conjSub g (F(U)) = F(conjSub g U)`, a restatement of
`Work.CORE4.FittingInConj` for the conjugation automorphism. -/
theorem conjSub_fittingIn {G : Type} [Group G] (U : Subgroup G) (g : G) :
    conjSub g (fittingIn U) = fittingIn (conjSub g U) :=
  (FittingInConj U (MulAut.conj g)).symm

/-- **Bender 1981, §4 (3).**  `F(U) ∩ M = (F(U) ∩ K) F`. -/
theorem SixThree (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      ∀ D : Work.GW2.Case2Data B, Work.GW2.Case2Pre B D →
        Work.GW2.fittingIn B.U ⊓ D.M = (Work.GW2.fittingIn B.U ⊓ D.K) ⊔ D.F := by
  intro G _ _ _ B D hpre
  refine le_antisymm ?_ ?_
  · -- `F(U) ∩ M ≤ (F(U) ∩ K) ⊔ F`
    intro x hx
    obtain ⟨hxA, hxM⟩ := Subgroup.mem_inf.mp hx
    -- `x ∈ U ⊓ M`
    have hxX : x ∈ B.U ⊓ D.M :=
      Subgroup.mem_inf.mpr ⟨Subgroup.map_subtype_le (fitting ↥B.U) hxA, hxM⟩
    -- `s ∈ H` and `s ∈ M`
    have hsH : D.s ∈ B.H := B.S_le_H D.s_mem_S
    have hsM : D.s ∈ D.M := layerIn_le D.M D.s_mem_layer
    -- `s` normalises `U` (`U ⊴ H`, `s ∈ H`)
    have hUnorm : ∀ y ∈ B.U, ∀ k ∈ B.H, k * y * k⁻¹ ∈ B.U := fun y hy k hk =>
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y k hy hk
    have hconjU : conjSub D.s B.U = B.U := by
      refine le_antisymm ?_ ?_
      · intro y hy
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
        rw [← hzy]
        simpa [MulAut.conj_apply] using hUnorm z hz D.s hsH
      · intro y hy
        refine Subgroup.mem_map.mpr ⟨D.s⁻¹ * y * D.s,
          by simpa using hUnorm y hy D.s⁻¹ (B.H.inv_mem hsH), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    -- `s` normalises `A = F(U)`
    have hconjA : ∀ y ∈ fittingIn B.U, D.s * y * D.s⁻¹ ∈ fittingIn B.U := by
      have hkey : conjSub D.s (fittingIn B.U) = fittingIn B.U := by
        rw [conjSub_fittingIn, hconjU]
      intro y hy
      have hmem : (MulAut.conj D.s) y ∈ conjSub D.s (fittingIn B.U) :=
        Subgroup.mem_map_of_mem (MulAut.conj D.s).toMonoidHom hy
      rw [hkey, MulAut.conj_apply] at hmem
      exact hmem
    -- `s` normalises `M`, `U` and `U ⊓ M`
    have hsN_U : D.s ∈ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact ⟨fun hy => hUnorm y hy D.s hsH, fun hy => by
        have h2 := hUnorm (D.s * y * D.s⁻¹) hy D.s⁻¹ (B.H.inv_mem hsH)
        rw [inv_inv, show D.s⁻¹ * (D.s * y * D.s⁻¹) * D.s = y by group] at h2
        exact h2⟩
    have hsN_M : D.s ∈ Subgroup.normalizer ((D.M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => D.M.mul_mem (D.M.mul_mem hsM hy) (D.M.inv_mem hsM), fun hy => ?_⟩
      have h : y = D.s⁻¹ * (D.s * y * D.s⁻¹) * D.s := by group
      rw [h]
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hsM) hy) hsM
    have hsNX : D.s ∈ Subgroup.normalizer (((B.U ⊓ D.M : Subgroup G)) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
        exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hsN_U y).mp hy1,
          (Subgroup.mem_normalizer_iff.mp hsN_M y).mp hy2⟩
      · intro hy
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
        exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hsN_U y).mpr hy1,
          (Subgroup.mem_normalizer_iff.mp hsN_M y).mpr hy2⟩
    -- `K ⊴ U ⊓ M` (Bender 1.5(iii), packaged as `LocalToolkit.c15`)
    have hOddX : Odd (Nat.card ↥(B.U ⊓ D.M)) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (inf_le_left : B.U ⊓ D.M ≤ B.U))
    have hKnorm : (D.K.subgroupOf (B.U ⊓ D.M)).Normal :=
      (I.toolkit.c15 G I.toolkit.ft (B.U ⊓ D.M) D.s D.s_order hOddX hsNX).2.2 D.K D.K_def |>.2.1
    -- decompose `x = k * b`
    obtain ⟨k, hkK, b, hbB0, hkb⟩ :=
      exists_mul_of_mem_of_normal_subgroupOf D.K_le D.B0_le hKnorm
        (Work.GW2.Case2Pre.U_eq B D hpre).symm x hxX
    -- `s` inverts `k` and fixes `b`
    have hk_inv : k ∈ invSet (B.U ⊓ D.M) D.s := by rw [← D.K_def]; exact hkK
    have hsk : MulAut.conj D.s k = k⁻¹ := by
      rw [MulAut.conj_apply]; exact hk_inv.2
    have hsb : MulAut.conj D.s b = b := by
      rw [MulAut.conj_apply]
      have hb_c : b ∈ Subgroup.centralizer ({D.s} : Set G) := by
        have h := hbB0
        rw [D.B0_def] at h
        exact (Subgroup.mem_inf.mp h).2
      have hbs : b * D.s = D.s * b := Subgroup.mem_centralizer_singleton_iff.mp hb_c
      rw [← hbs]; group
    -- `k ^ 2 = x * (s x⁻¹ s⁻¹) ∈ F(U)`
    have hk2 : k ^ 2 ∈ fittingIn B.U := by
      have hxx : x * (D.s * x⁻¹ * D.s⁻¹) ∈ fittingIn B.U :=
        (fittingIn B.U).mul_mem hxA (hconjA x⁻¹ ((fittingIn B.U).inv_mem hxA))
      have h1 : D.s * x⁻¹ * D.s⁻¹ = b⁻¹ * k := by
        have hxconj : MulAut.conj D.s x = k⁻¹ * b := by
          rw [← hkb, map_mul, hsk, hsb]
        rw [← MulAut.conj_apply, map_inv, hxconj]
        group
      have heq : k ^ 2 = x * (D.s * x⁻¹ * D.s⁻¹) := by
        rw [h1, ← hkb, pow_two]
        group
      rwa [← heq] at hxx
    -- `k ∈ F(U)`: `k ^ 2 ∈ F(U)` and `k` has odd order
    have hkA : k ∈ fittingIn B.U := by
      have hdvd : orderOf k ∣ Nat.card ↥B.U :=
        Subgroup.orderOf_dvd_natCard B.U (Case2Data.K_le_U B D hkK)
      have hodd : Odd (orderOf k) := Odd.of_dvd_nat B.U_odd hdvd
      obtain ⟨t, ht⟩ := hodd
      have h2dvd : 2 ∣ orderOf k + 1 := ⟨t + 1, by omega⟩
      have hkey : k = (k ^ 2) ^ ((orderOf k + 1) / 2) := by
        rw [← pow_mul, Nat.mul_div_cancel' h2dvd, pow_succ, pow_orderOf_eq_one, one_mul]
      rw [hkey]
      exact (fittingIn B.U).pow_mem hk2 _
    -- `b = k⁻¹ x ∈ F(U)`
    have hbA : b ∈ fittingIn B.U := by
      have hb_eq : b = k⁻¹ * x := by rw [← hkb]; group
      rw [hb_eq]
      exact (fittingIn B.U).mul_mem ((fittingIn B.U).inv_mem hkA) hxA
    rw [← hkb]
    refine Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hkA, hkK⟩) ?_
    rw [D.F_def]
    exact Subgroup.mem_inf.mpr ⟨hbB0, hbA⟩
  · -- `(F(U) ∩ K) ⊔ F ≤ F(U) ∩ M`
    refine sup_le (le_inf inf_le_left (le_trans inf_le_right D.K_le_M)) ?_
    exact le_inf D.F_le_fitting (le_trans D.F_le_UinfM inf_le_right)

end Work.CORE4
