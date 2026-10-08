/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Submission.Work.GLUE.Bridge

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# GLUE: the `p`-core `O_p(G)` in our own notation

`Work.GW2.pCore p G` is the join of the normal `p`-subgroups of `G`, wrapped in
`normalCore`; `Bridge.lean` identifies it with the library's `opCore`.  This file records
the elementary API of `pCore` *without* any reference to the library, so that consumer areas
never have to unfold the definition or reach into `OddOrder.Isaacs.Ch01`.
-/

namespace Work.GW2

variable {G : Type*} [Group G]

/-- **Universal property of `O_p(G)`.** Every normal `p`-subgroup lies in `pCore p G`.
(No finiteness and no primality of `p` are needed: this is `le_sSup` followed by
`Subgroup.normal_le_normalCore`, i.e. `O_p(G)` is the *largest* normal `p`-subgroup.) -/
theorem le_pCore_of_normal_isPGroup {p : ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p N) : N ≤ pCore p G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- `pCore p G` is a `p`-group. -/
theorem pCore_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] : IsPGroup p ↥(pCore p G) := by
  rw [pCore_eq_opCore]
  exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G

/-- `O_p(G)` is contained in every Sylow `p`-subgroup. -/
theorem pCore_le_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    pCore p G ≤ (P : Subgroup G) := by
  rw [pCore_eq_opCore]
  exact OddOrder.Isaacs.Ch01.opCore_le P

/-- Membership in `O_p(G)` is membership in every Sylow `p`-subgroup. -/
theorem mem_pCore_iff [Finite G] {p : ℕ} [Fact p.Prime] {x : G} :
    x ∈ pCore p G ↔ ∀ P : Sylow p G, x ∈ (P : Subgroup G) := by
  rw [pCore_eq_opCore]
  exact OddOrder.Isaacs.Ch01.mem_opCore

/-- `O_p(G) ≤ F(G)`. -/
theorem pCore_le_fitting [Finite G] {p : ℕ} [Fact p.Prime] : pCore p G ≤ fitting G :=
  Subgroup.normal_le_normalCore.mpr
    (le_sSup ⟨pCore_normal p G, (pCore_isPGroup (G := G)).isNilpotent⟩)

end Work.GW2
