import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.caseC_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# General case-c lemmas, independent of `caseC_data`

`Work.PSU3.StageA.caseC_Q0sub_subgroupOf_iff_sq` records that inside `Q` the subgroup
`Q₀ = Q0sub H` is exactly the set of elements of order `≤ 2` (Peterfalvi II Ch. II §4 / Ch. V §1).
It lived in `Submission/Work/PSU3/StageA/caseC_data.lean`; it is moved here so that the
`Direct/` chain (the Feit–Thompson-free version of the case-b analysis) can use it without
importing `caseC_data` — which in turn imports that chain.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- Inside `Q`, the subgroup `Q₀sub H = ⟨Inv H ∪ {1}⟩` is the set of elements of order `≤ 2`
(Peterfalvi II Ch. II §4 / Ch. V §1: the involutions of `H` lie in `Q` and are the elements of
order `2` of `Q`). -/
theorem caseC_Q0sub_subgroupOf_iff_sq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 := by
  intro x
  constructor
  · intro hx
    exact Subtype.ext (caseC_mem_Q0sub_iff hS hC4 (x : G) hx)
  · intro hx
    have hxG : (x : G) * (x : G) = 1 := by
      have h := congrArg Subtype.val hx
      simpa [Subgroup.coe_mul] using h
    rcases eq_or_ne (x : G) 1 with h1 | h1
    · rw [h1]; exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H)
    · have ho : orderOf (x : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxG) h1
      exact Work.ThmF.Q0_le_Q0sub H
        (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le x.2, ho⟩)

end Work.PSU3.StageA
