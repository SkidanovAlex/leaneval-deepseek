/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The kernel copy `flowEKer` of a graded piece *is* the graded piece `E(m,τ)`

Schmidt–Wingberg's Step 3 of Theorem 15 works with the level projection

`flowGroupProj p G m i j : F(m)/F(m)^{(τ+1)} ⋊ G →* F(m)/F(m)^{(τ)} ⋊ G`,  `τ+1 = tauSucc i j`,

whose kernel `flowEKer p G m i j` is *the copy of the graded piece* `E p G m i j` inside the
level-`τ+1` group (see `Submission/Work/SSGRoute/ProperStageDefs.lean`).  This module makes that
statement precise: the subgroup `flowEKer` is isomorphic, as a group, to the graded piece

`refinedQuotient p (freeOperatorGroup G m) i j = F(m)^{(τ)} / F(m)^{(τ+1)}`.

The proof factorises the identification into two independent steps:

* `flowEKerLift p G m i j : F(m)^{(τ)} →* ker(flowQuotientProj p G m i j)` is the map induced by
  the inclusion `F(m)^{(τ)} ↪ F(m)`, followed by the quotient map onto
  `F(m)/F(m)^{(τ+1)}`; its kernel is `F(m)^{(τ+1)}` and it is onto the kernel of the projection
  (`flowEKerLift_ker`, `flowEKerLift_surjective`).  The first isomorphism theorem then identifies
  `F(m)^{(τ)}/F(m)^{(τ+1)}` with `ker(flowQuotientProj)`.
* the kernel of `flowGroupProj` is the image of `ker(flowQuotientProj)` under the (injective)
  inclusion of the free factor `flowInl` (`flowEKer_eq_map_ker`), so the two have the same
  underlying group.
-/

import Mathlib
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.flowEKer_comm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option maxHeartbeats 800000

/-! ## The map `F(m)^{(τ)} →* ker(flowQuotientProj)` -/

/-- The composite `F(m)^{(τ)} ↪ F(m) ↠ F(m)/F(m)^{(τ+1)}` (the quotient map onto the level-`τ+1`
quotient), whose image in fact lies in the kernel of the level projection. -/
noncomputable def flowEKerMap (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    ↥(flowTerm p G m i j) →*
      (flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) :=
  (QuotientGroup.mk'
      ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤)).comp
    (Subgroup.inclusion (le_top : flowTerm p G m i j ≤ ⊤))

/-- The map `F(m)^{(τ)} →* ker(flowQuotientProj p G m i j)` induced by the inclusion, restricted to
the copy of the graded piece inside the level-`τ+1` group. -/
noncomputable def flowEKerLift (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    ↥(flowTerm p G m i j) →* ↥((flowQuotientProj p G m i j).ker) :=
  MonoidHom.codRestrict (flowEKerMap p G m i j) ((flowQuotientProj p G m i j).ker)
    (fun t => by
      rw [MonoidHom.mem_ker]
      change flowQuotientProj p G m i j (flowEKerMap p G m i j t) = 1
      rw [show flowEKerMap p G m i j t =
          (QuotientGroup.mk'
            ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤))
            (Subgroup.inclusion (le_top : flowTerm p G m i j ≤ ⊤) t) from rfl]
      rw [flowQuotientProj_mk]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_subgroupOf]
      exact t.2)

/-- The kernel of `flowEKerLift` is the next term of the refinement, i.e. the graded piece is the
quotient `F(m)^{(τ)}/F(m)^{(τ+1)}`. -/
theorem flowEKerLift_ker (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    (flowEKerLift p G m i j).ker =
      (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf (flowTerm p G m i j) := by
  ext t
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h2 : flowEKerMap p G m i j t = 1 := Subtype.ext_iff.mp h
    rw [show flowEKerMap p G m i j t =
        (QuotientGroup.mk'
          ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤))
          (Subgroup.inclusion (le_top : flowTerm p G m i j ≤ ⊤) t) from rfl] at h2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro h
    apply Subtype.ext
    change flowEKerMap p G m i j t = 1
    rw [show flowEKerMap p G m i j t =
        (QuotientGroup.mk'
          ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤))
          (Subgroup.inclusion (le_top : flowTerm p G m i j ≤ ⊤) t) from rfl]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [Subgroup.mem_subgroupOf]
    exact h

/-- `flowEKerLift` is onto the kernel of the level projection: every class in the kernel is the
class of an element of `F(m)^{(τ)}`. -/
theorem flowEKerLift_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowEKerLift p G m i j) := by
  intro y
  have hy : (y : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2)
      ∈ Subgroup.map
          (QuotientGroup.mk'
            ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤))
          ((flowTerm p G m i j).subgroupOf ⊤) := by
    rw [← flowQuotientProj_ker_eq p G m i j]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  let t : ↥(flowTerm p G m i j) :=
    ⟨(x : Work.Shrinking.freeOperatorGroup G m), Subgroup.mem_subgroupOf.mp hx⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change flowEKerMap p G m i j t = (y : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2)
  have ht : Subgroup.inclusion (le_top : flowTerm p G m i j ≤ ⊤) t = x := Subtype.ext rfl
  rw [show flowEKerMap p G m i j t =
      (QuotientGroup.mk' ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf ⊤))
        (Subgroup.inclusion (le_top : flowTerm p G m i j ≤ ⊤) t) from rfl]
  rw [ht]
  exact hxy

/-! ## The requested statement -/

/-- **The kernel copy of the graded piece is the graded piece.**  The kernel of the level
projection `flowGroupProj p G m i j` is isomorphic to
`refinedQuotient p (freeOperatorGroup G m) i j = F(m)^{(τ)}/F(m)^{(τ+1)}`. -/
theorem flowEKer_equiv_refinedQuotient (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Nonempty (Work.SSGRoute.flowEKer p G m i j ≃*
      Work.CohomologicalShrinking.refinedQuotient p
        (Work.Shrinking.freeOperatorGroup G m) i j) := by
  -- First isomorphism theorem: `F(m)^{(τ)}/F(m)^{(τ+1)} ≃* ker(flowQuotientProj)`.
  have eA : refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j ≃*
      ↥((flowQuotientProj p G m i j).ker) :=
    (QuotientGroup.quotientMulEquivOfEq (flowEKerLift_ker p G m i j)).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective (flowEKerLift p G m i j)
        (flowEKerLift_surjective p G m i j))
  -- The kernel of the level projection is the image of `ker(flowQuotientProj)` under `flowInl`.
  have eB : ↥(flowEKer p G m i j) ≃* ↥((flowQuotientProj p G m i j).ker) :=
    (flowEKer_eq_map_ker p G m i j).symm ▸
      (Subgroup.equivMapOfInjective ((flowQuotientProj p G m i j).ker)
        (flowInl p G m (tauSucc i j).1 (tauSucc i j).2)
        (flowInl_injective p G m (tauSucc i j).1 (tauSucc i j).2)).symm
  exact ⟨eB.trans eA.symm⟩

end Work.SSGRoute
