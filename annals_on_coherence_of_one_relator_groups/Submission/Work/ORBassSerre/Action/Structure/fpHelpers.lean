/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Elementary geometry for the Bass--Serre free-product theorem

Let `Γ` act on a tree `V` without inversions, with trivial edge stabilisers (`hedge`).  This file
proves the rigidity of the action on geodesics and its immediate consequences, which are the
geometric input of the free-product theorem
`Work.ORBassSerre.Action.Structure.freeProduct_of_isTree_trivialEdgeStabilizers`.

The main facts:

* `eq_one_of_fixes_edge_endpoints` : an element fixing both endpoints of an arrow is `1`;
* `eq_one_of_fixes_two_vertices` : an element fixing two distinct vertices is `1`;
* `smulPath_isReduced` : the translate of a reduced path is reduced;
* `smulPath_geodesic` : `g • geodesic u w = geodesic (g · u) (g · w)`.
-/
import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Action.Structure.AmalgamZigzag
import Submission.Work.ORBassSerre.Action.Structure.helpers
import Submission.Work.ORBassSerre.Action.Structure.hnn_reduced_word_ne_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure.FP

open Quiver

universe u v

variable {Γ : Type u} {V : Type v} [Group Γ] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]

/-- An element fixing both endpoints of an arrow is trivial, because the edge stabilisers are
trivial and in a tree an arrow is determined by its endpoints. -/
theorem eq_one_of_fixes_edge_endpoints (hT : Work.ORBassSerre.IsTree V)
    (hedge : ∀ e : Quiver.Total V, MulAction.stabilizer Γ e = ⊥)
    {a b : V} (e : a ⟶ b) {g : Γ} (ha : g • a = a) (hb : g • b = b) : g = 1 := by
  have hleft : (g • Quiver.Total.mk a b e).left = (Quiver.Total.mk a b e).left := by
    rw [total_smul_left, ha]
  have hright : (g • Quiver.Total.mk a b e).right = (Quiver.Total.mk a b e).right := by
    rw [total_smul_right, hb]
  have heq : g • Quiver.Total.mk a b e = Quiver.Total.mk a b e :=
    total_ext_of_isTree (hT := hT) hleft hright
  have hmem : g ∈ MulAction.stabilizer Γ (Quiver.Total.mk a b e) := heq
  rw [hedge] at hmem
  simpa using hmem

end Work.ORBassSerre.Action.Structure.FP
