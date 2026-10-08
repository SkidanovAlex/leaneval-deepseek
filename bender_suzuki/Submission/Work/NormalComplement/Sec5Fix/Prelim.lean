/-
# `Work.NormalComplement.Sec5Fix.Prelim` — imports shared by the `Sec5Fix` leaves

This module only *re-exports* library modules needed by the leaves of the
`Work.NormalComplement.Sec5Fix` development of Peterfalvi I Ch. III §5 Prop. 2 (a)
(`orderOf (u * t) ∈ {3, 5}`), together with a few elementary helper lemmas.

The reason for its existence is mechanical: requests for the leaves must list their imports as
paths relative to `Submission/Work/`, so the modules *outside* `Submission/Work/`
(`Submission.Blueprint.Interfaces`, the `Commons` port, ...) are unreachable directly.
Importing this module makes them available.
-/
import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.ThreePoints.P3NeBot.p3b_glue
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot
import Submission.Work.ThreePoints.P3NeBot.prop1b_brsz
import Submission.Work.Reductions.OddResidual
import Submission.Work.Reductions.hasFourGroup_quotient
import Submission.Work.Models.fm1src.Submission.Commons.GroupTheory.GroupAction.isCoatom_stabilizer_of_forall_pair
import Submission.Work.Models.fm1src.Submission.Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le
import Submission.Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.Sec5Fix

/-- `HasFourGroup` is transported by group isomorphisms. -/
theorem hasFourGroup_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Submission.Blueprint.HasFourGroup H) : Submission.Blueprint.HasFourGroup G := by
  obtain ⟨a, b, ha, hb, hne, hc⟩ := h
  have key : ∀ x : H, orderOf x = 2 → orderOf (e.symm x) = 2 := fun x hx =>
    (orderOf_injective (e.symm : H →* G) e.symm.injective x).trans hx
  refine ⟨e.symm a, e.symm b, key a ha, key b hb, ?_, ?_⟩
  · intro h1; exact hne (e.symm.injective h1)
  · calc e.symm a * e.symm b = e.symm (a * b) := (map_mul (e.symm : H →* G) a b).symm
      _ = e.symm (b * a) := by rw [hc]
      _ = e.symm b * e.symm a := map_mul (e.symm : H →* G) b a

end Work.NormalComplement.Sec5Fix
