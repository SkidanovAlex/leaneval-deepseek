/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — basic API of the §4 objects

The objects of Bender §4 are the fields of `Case2Data B` (`M, X, s, K, B₀, F`) together with
`Case2Pre B D` (§4 (1)–(5)) and the further fields of `Case2Ctx B` (§4 (6), the exclusion of `A₇`
and (9)).  Everything in §4 uses these objects, so this file records the immediate consequences
that the leaf proofs keep needing, in the `Case2Data` / `Case2Pre` namespaces:

* `D.K = I_{U∩M}(s)`, so `s` inverts `K` and `K ⊆ U ∩ M`  (`K_inv`, `K_le`);
* `D.B₀ = C_{U∩M}(s) ⊆ U ∩ M` and `D.F = B₀ ∩ F(U) ⊆ B₀ ⊆ U ∩ M ⊆ U` (`F_le_B0`, `F_le_U`);
* `D.F ≤ F(U)` (`F_le_fitting`), `D.X ≤ U` (`X_le_U`), `D.s ∈ S ∩ E(M)`, `D.M ≠ ⊤`;
* named accessors for the eight conjuncts of `Case2Pre` (`Case2Pre.not_H_le`, `Case2Pre.K_cyclic`,
  `Case2Pre.N_F`, …).
-/
import Submission.Work.CORE4.Defs

namespace Work.GW2

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The fields of `Case2Data` -/

theorem Case2Data.M_ne_top (B : BenderSetup G) (D : Case2Data B) : D.M ≠ ⊤ :=
  D.M_coatom.ne_top

theorem Case2Data.s_mem_S (B : BenderSetup G) (D : Case2Data B) : D.s ∈ (B.S : Subgroup G) :=
  (Subgroup.mem_inf.mp D.s_mem).1

theorem Case2Data.s_mem_layer (B : BenderSetup G) (D : Case2Data B) : D.s ∈ layerIn D.M :=
  (Subgroup.mem_inf.mp D.s_mem).2

/-- `K ⊆ U ∩ M`, because `K = I_{U∩M}(s)` by definition. -/
theorem Case2Data.K_le (B : BenderSetup G) (D : Case2Data B) : D.K ≤ B.U ⊓ D.M := by
  intro x hx
  have hx' : x ∈ invSet (B.U ⊓ D.M) D.s := by rw [← D.K_def]; exact hx
  exact hx'.1

theorem Case2Data.K_le_U (B : BenderSetup G) (D : Case2Data B) : D.K ≤ B.U :=
  le_trans (D.K_le B) inf_le_left

theorem Case2Data.K_le_M (B : BenderSetup G) (D : Case2Data B) : D.K ≤ D.M :=
  le_trans (D.K_le B) inf_le_right

/-- `s` inverts `K = I_{U∩M}(s)`. -/
theorem Case2Data.K_inv (B : BenderSetup G) (D : Case2Data B) : Inverts D.s D.K := by
  intro x hx
  have hx' : x ∈ invSet (B.U ⊓ D.M) D.s := by rw [← D.K_def]; exact hx
  exact hx'.2

theorem Case2Data.B0_le (B : BenderSetup G) (D : Case2Data B) : D.B0 ≤ B.U ⊓ D.M := by
  rw [D.B0_def]
  exact inf_le_left

theorem Case2Data.F_le_B0 (B : BenderSetup G) (D : Case2Data B) : D.F ≤ D.B0 := by
  rw [D.F_def]
  exact inf_le_left

theorem Case2Data.F_le_U (B : BenderSetup G) (D : Case2Data B) : D.F ≤ B.U :=
  le_trans (D.F_le_B0 B) (le_trans (D.B0_le B) inf_le_left)

theorem Case2Data.F_le_UinfM (B : BenderSetup G) (D : Case2Data B) : D.F ≤ B.U ⊓ D.M :=
  le_trans (D.F_le_B0 B) (D.B0_le B)

/-- `F ≤ F(U)`. -/
theorem Case2Data.F_le_fitting (B : BenderSetup G) (D : Case2Data B) : D.F ≤ fittingIn B.U := by
  rw [D.F_def]
  exact inf_le_right

/-- `X ≤ U` (from `Case2`'s `X ≤ F(U)`). -/
theorem Case2Data.X_le_U (B : BenderSetup G) (D : Case2Data B) : D.X ≤ B.U := by
  have h : fittingIn B.U ≤ B.U := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.2
  exact le_trans D.X_le h

/-! ## The conjuncts of `Case2Pre` (§4 (1)–(5)) -/

theorem Case2Pre.not_H_le (B : BenderSetup G) (D : Case2Data B) (h : Case2Pre B D) :
    ¬ B.H ≤ D.M := h.1

theorem Case2Pre.oneClass (B : BenderSetup G) (D : Case2Data B) (h : Case2Pre B D) :
    OneInvClassIn (layerIn D.M) := h.2.1

theorem Case2Pre.K_cyclic (B : BenderSetup G) (D : Case2Data B) (h : Case2Pre B D) :
    IsCyclic D.K := h.2.2.1

theorem Case2Pre.U_eq (B : BenderSetup G) (D : Case2Data B) (h : Case2Pre B D) :
    B.U ⊓ D.M = D.K ⊔ D.B0 := h.2.2.2.1

theorem Case2Pre.F_ne (B : BenderSetup G) (D : Case2Data B) (h : Case2Pre B D) : D.F ≠ ⊥ :=
  h.2.2.2.2.1

theorem Case2Pre.F_cent (B : BenderSetup G) (D : Case2Data B) (h : Case2Pre B D) :
    D.F ≤ centralizer ((layerIn D.M : Subgroup G) : Set G) := h.2.2.2.2.2.1

theorem Case2Pre.N_F (B : BenderSetup G) (D : Case2Data B) (h : Case2Pre B D) :
    normalizer (D.F : Set G) = D.M := h.2.2.2.2.2.2.1

theorem Case2Pre.B0_eq (B : BenderSetup G) (D : Case2Data B) (h : Case2Pre B D) :
    D.B0 = B.U ⊓ centralizer ({D.s} : Set G) := h.2.2.2.2.2.2.2

/-- `F ≠ ⊥` together with `F ≤ B₀` gives a nontrivial element to conjugate. -/
theorem Case2Data.exists_ne_one_of_F (B : BenderSetup G) (D : Case2Data B)
    (hF : D.F ≠ ⊥) : ∃ x ∈ D.F, x ≠ 1 := by
  by_contra hcon
  apply hF
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  exact hcon ⟨x, hx, hx1⟩

end Work.GW2
