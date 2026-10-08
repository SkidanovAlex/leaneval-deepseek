import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Global `Fintype` instances for subgroups

`Fintype ↥H` for a subgroup `H ≤ X` is Mathlib's
`Subgroup.instFintypeSubtypeMemOfDecidablePred`, whose implicit `DecidablePred (· ∈ H)`
argument is only synthesised when `Classical.propDecidable` is in scope (for instance after
`open Classical`).  Statements that mention `↥H` for a subgroup `H` therefore fail to
elaborate in files that do not open `Classical`.

This module registers that instance at low priority, so that any module importing it can
elaborate such statements, while the Mathlib instance keeps precedence wherever it is
available.
-/

noncomputable instance instFintypeSubtypeMemSubgroup {X : Type*} [Group X]
    [Fintype X] (H : Subgroup X) : Fintype ↥H := by
  classical
  exact inferInstance

attribute [instance 10] instFintypeSubtypeMemSubgroup
