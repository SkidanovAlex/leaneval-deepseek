import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

theorem omega_mono_index {G : Type*} [Group G] (p i : ℕ) (P : Subgroup G) :
    Work.PGroup.omega p i P ≤ Work.PGroup.omega p (i + 1) P := by
  rw [omega, Subgroup.closure_le]
  rintro x ⟨hx, hx1⟩
  refine Subgroup.subset_closure ⟨hx, ?_⟩
  rw [pow_succ, pow_mul, hx1, one_pow]

end Work.PGroup
