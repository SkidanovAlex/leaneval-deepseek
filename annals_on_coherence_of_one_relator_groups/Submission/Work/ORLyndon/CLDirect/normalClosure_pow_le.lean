import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs

namespace Work.ORLyndon.CLDirect

/-- `⟪u^l⟫ ≤ ⟪u⟫`. Sketch: `Subgroup.normalClosure_le_normal` applied to `pow_mem (Subgroup.subset_normalClosure rfl) l`. -/
theorem normalClosure_pow_le {X : Type*} (u : FreeGroup X) (l : ℕ) :
    Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) ≤
      Subgroup.normalClosure ({u} : Set (FreeGroup X)) := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact pow_mem (Subgroup.subset_normalClosure (Set.mem_singleton u)) l

end Work.ORLyndon.CLDirect
