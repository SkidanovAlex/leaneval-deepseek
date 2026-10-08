/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.Thm26bVocab

/-!
# CORE2A: design pass 14, `P2` — lifting centralizers through the odd kernel `Z(E(Ĥ))`

`Work.CORE2A.c14_lift` is the "lifting through the odd kernel" step of Bender 1981 p. 220
(`Submission/Work/_design_gw/Core14.lean`, `c14_lift`, and `NOTES_LEAD_gw_design14.md` §P2):

if `E := E(Ĥ)`, `Z := Z(E)` and `φ : SE → PGL₂(q)` is the quotient of `Thm26bAutProp` (a) with
kernel `Z` and `φ(E) = L₂(q)`, then for any involution `u ∈ SE` and any `x ∈ SE` with
`(x : G) ∈ E` whose image `φ x` commutes with `φ u`, there is `x' ∈ E` with `x' u = u x'` in `G`
and `φ x' = φ x`.

Proof (`x' = x * y`, `y ∈ Z` a square root of an explicit element of `Z`):

* `w := x⁻¹ (u x u⁻¹) ∈ SE` has `φ w = (φ x)⁻¹ (φ u · φ x · (φ u)⁻¹) = (φ x)⁻¹ φ x = 1`, since
  `(φ u)² = 1` and `φ u` commutes with `φ x`; hence `z := (w : G) = (x : G)⁻¹ (u x u⁻¹)` lies in
  `zE B = Z`, i.e. `u x u⁻¹ = x z`.
* Applying `u (_) u⁻¹` to that identity and using `u² = 1` gives `z · (u z u⁻¹) = 1`, i.e.
  `u z u⁻¹ = z⁻¹` (`u` inverts `z`, because `z = x⁻¹ · (u x u⁻¹)` and conjugation by `u` is an
  involution).
* `|Z| = Nat.card ↥(zE B)` is odd (`Work.CORE2A.zE_odd`), so `y := z^((|Z|+1)/2)` satisfies
  `y² = z^{|Z|+1} = z`.  Then `u y u⁻¹ = (u z u⁻¹)^n = (z^n)⁻¹ = y⁻¹`, so
  `u (x y) u⁻¹ = (x z)·y⁻¹ = x·(z y⁻¹) = x y` using `z y⁻¹ = y` (`y² = z`).
* `φ(x y) = φ x`, since `y ∈ Z = ker φ`, and `x y ∈ E ≤ SE` because `zE B ≤ E`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

theorem c14_lift (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} {p k : ℕ} [Fact p.Prime] (D : Work.GW2.PGLData B p k) {u : G} (hu : u ∈ Work.GW2.SE B) (hu2 : u * u = 1) (x : ↥(Work.GW2.SE B)) (hxE : (x : G) ∈ Work.GW2.layerIn B.Hhat) (hc : D.φ x * D.φ ⟨u, hu⟩ = D.φ ⟨u, hu⟩ * D.φ x) : ∃ x' : ↥(Work.GW2.SE B), (x' : G) ∈ Work.GW2.layerIn B.Hhat ∧ (x' : G) * u = u * x' ∧ D.φ x' = D.φ x := by
  by_cases hne : Work.GW2.layerIn B.Hhat = ⊥
  · -- `E = 1`, so `x = 1` and `x' = x` works.
    have hx1 : (x : G) = 1 := by
      have h := hxE
      rw [hne] at h
      simpa using h
    refine ⟨x, hxE, ?_, rfl⟩
    show (x : G) * u = u * (x : G)
    rw [hx1, one_mul, mul_one]
  · have hZodd : Odd (Nat.card ↥(Work.GW2.zE B)) := Work.CORE2A.zE_odd T hFT hbc B hne
    have hzEle : Work.GW2.zE B ≤ Work.GW2.layerIn B.Hhat := Work.CORE2A.zE_le
    have hzSE : Work.GW2.zE B ≤ Work.GW2.SE B := hzEle.trans Work.CORE2A.layerIn_le_SE
    -- `w := x⁻¹ (u x u⁻¹)` lies in `ker φ = Z(E)`.
    have hwphi : D.φ (x⁻¹ * (⟨u, hu⟩ * x * ⟨u, hu⟩⁻¹)) = 1 := by
      have hu2S : (⟨u, hu⟩ : ↥(Work.GW2.SE B)) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
      have hpu2 : D.φ ⟨u, hu⟩ * D.φ ⟨u, hu⟩ = 1 := by
        rw [← map_mul, hu2S, map_one]
      have hpuinv : (D.φ ⟨u, hu⟩)⁻¹ = D.φ ⟨u, hu⟩ := inv_eq_of_mul_eq_one_right hpu2
      have h1 : D.φ (x⁻¹ * (⟨u, hu⟩ * x * ⟨u, hu⟩⁻¹)) =
          (D.φ x)⁻¹ * (D.φ ⟨u, hu⟩ * D.φ x * (D.φ ⟨u, hu⟩)⁻¹) := by
        simp only [map_mul, map_inv]
      rw [h1, hpuinv]
      have h2 : D.φ ⟨u, hu⟩ * D.φ x * D.φ ⟨u, hu⟩ = D.φ x := by
        rw [← hc, mul_assoc, hpu2, mul_one]
      rw [h2, inv_mul_cancel]
    have hzmem : ((x⁻¹ * (⟨u, hu⟩ * x * ⟨u, hu⟩⁻¹) : ↥(Work.GW2.SE B)) : G) ∈ Work.GW2.zE B := by
      have hker : (x⁻¹ * (⟨u, hu⟩ * x * ⟨u, hu⟩⁻¹) : ↥(Work.GW2.SE B)) ∈ D.φ.ker :=
        MonoidHom.mem_ker.mpr hwphi
      rw [D.ker] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    have hzcoe : ((x⁻¹ * (⟨u, hu⟩ * x * ⟨u, hu⟩⁻¹) : ↥(Work.GW2.SE B)) : G) =
        (x : G)⁻¹ * (u * (x : G) * u⁻¹) := rfl
    obtain ⟨z, hz, hzdef⟩ : ∃ z : G, z ∈ Work.GW2.zE B ∧
        z = (x : G)⁻¹ * (u * (x : G) * u⁻¹) :=
      ⟨_, hzmem, hzcoe⟩
    -- `u x u⁻¹ = x z`
    have hxz : (x : G) * z = u * (x : G) * u⁻¹ := by
      rw [hzdef]; group
    -- `u` inverts `z`
    have hzu : u * z * u⁻¹ = z⁻¹ := by
      have h6 : z * (u * z * u⁻¹) = 1 := by
        have h7 : (x : G) * (z * (u * z * u⁻¹)) = (x : G) * 1 := by
          calc (x : G) * (z * (u * z * u⁻¹))
              = ((x : G) * z) * (u * z * u⁻¹) := by group
            _ = (u * (x : G) * u⁻¹) * (u * z * u⁻¹) := by rw [hxz]
            _ = u * ((x : G) * z) * u⁻¹ := by group
            _ = u * (u * (x : G) * u⁻¹) * u⁻¹ := by rw [hxz]
            _ = (x : G) * 1 := by
                have hu_inv2 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
                have h3 : u * (u * (x : G) * u⁻¹) * u⁻¹ =
                    (u * u) * (x : G) * (u⁻¹ * u⁻¹) := by group
                rw [h3, hu2, hu_inv2]; group
        exact mul_left_cancel h7
      exact (inv_eq_of_mul_eq_one_right h6).symm
    -- `y := z^((|Z|+1)/2)` is a square root of `z` in `Z`.
    have hzpow : z ^ Nat.card ↥(Work.GW2.zE B) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp (Subgroup.orderOf_dvd_natCard (Work.GW2.zE B) hz)
    let n : ℕ := (Nat.card ↥(Work.GW2.zE B) + 1) / 2
    have h2n : 2 * n = Nat.card ↥(Work.GW2.zE B) + 1 := by
      have h1 : 2 * (Nat.card ↥(Work.GW2.zE B) / 2 + 1) = Nat.card ↥(Work.GW2.zE B) + 1 := by
        have hN := Nat.two_mul_div_two_add_one_of_odd hZodd
        omega
      have h2 : (Nat.card ↥(Work.GW2.zE B) + 1) / 2 = Nat.card ↥(Work.GW2.zE B) / 2 + 1 := by
        rw [← h1, Nat.mul_div_right _ (by norm_num : 0 < 2)]
      show 2 * ((Nat.card ↥(Work.GW2.zE B) + 1) / 2) = Nat.card ↥(Work.GW2.zE B) + 1
      rw [h2, h1]
    have hsq : z ^ n * z ^ n = z := by
      rw [← pow_add]
      have hnn : n + n = 2 * n := by omega
      rw [hnn, h2n, pow_succ, hzpow, one_mul]
    have huz : u * z ^ n * u⁻¹ = (z ^ n)⁻¹ := by
      rw [show u * z ^ n * u⁻¹ = (u * z * u⁻¹) ^ n from
            (conj_pow (a := u) (b := z) (i := n)).symm, hzu, inv_pow]
    have hzy : z * (z ^ n)⁻¹ = z ^ n := by
      apply mul_right_cancel (b := z ^ n)
      rw [mul_assoc, inv_mul_cancel, mul_one, hsq]
    -- `x * y` is fixed by conjugation by `u`.
    have hfix : u * ((x : G) * z ^ n) * u⁻¹ = (x : G) * z ^ n := by
      rw [show u * ((x : G) * z ^ n) * u⁻¹ =
            (u * (x : G) * u⁻¹) * (u * z ^ n * u⁻¹) from by group, ← hxz, huz]
      rw [show (x : G) * z * (z ^ n)⁻¹ = (x : G) * (z * (z ^ n)⁻¹) from by group, hzy]
    have hcomm : u * ((x : G) * z ^ n) = ((x : G) * z ^ n) * u := by
      have h := congrArg (fun t => t * u) hfix
      simpa [mul_assoc] using h
    have hmem : z ^ n ∈ Work.GW2.SE B := hzSE (pow_mem hz n)
    refine ⟨x * ⟨z ^ n, hmem⟩, ?_, ?_, ?_⟩
    · show (x : G) * z ^ n ∈ Work.GW2.layerIn B.Hhat
      exact mul_mem hxE (hzEle (pow_mem hz n))
    · show ((x : G) * z ^ n) * u = u * ((x : G) * z ^ n)
      exact hcomm.symm
    · rw [map_mul]
      have hphi1 : D.φ ⟨z ^ n, hmem⟩ = 1 := by
        rw [← MonoidHom.mem_ker, D.ker]
        exact Subgroup.mem_subgroupOf.mpr (pow_mem hz n)
      rw [hphi1, mul_one]

end Work.CORE2A
