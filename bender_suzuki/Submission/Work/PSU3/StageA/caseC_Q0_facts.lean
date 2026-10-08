import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.corProp2
import Submission.Work.PSU3.StageA.caseC_module_data

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- Part 1 of `caseC_Q0_facts`: inside `Q`, the group `Q₀sub H = ⟨Inv H⟩` is exactly the set of
elements of order `≤ 2`.

* `→` is Peterfalvi II Ch. V §1 Prop. 1 (c) (`Q₀sub H` is elementary abelian, `Q0sub_elementary`);
* `←` is trivial: an `x ∈ Q ≤ H` with `x² = 1` is either `1` or an involution of `H`. -/
theorem caseC_Q0sub_mem_iff {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 := by
  have hmem : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H → (x : G) * (x : G) = 1 :=
    fun x hx => caseC_mem_Q0sub_iff hS hC4 (x : G) hx
  intro x
  constructor
  · intro hx
    exact Subtype.ext (hmem x hx)
  · intro hx
    have hxG : (x : G) * (x : G) = 1 := by
      have h := congrArg Subtype.val hx
      simpa [Subgroup.coe_mul] using h
    by_cases h1 : (x : G) = 1
    · rw [h1]
      exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H)
    · have ho : orderOf (x : G) = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hxG) h1
      exact Work.ThmF.Q0_le_Q0sub H
        (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le x.2, ho⟩)

-- Superseded (2026): the hole-tainted `caseC_sq_mem_Q0sub` was removed by the hole sweep.

-- Superseded (2026): the hole-tainted `caseC_Q0_facts` was removed by the hole sweep.

end Work.PSU3.StageA
