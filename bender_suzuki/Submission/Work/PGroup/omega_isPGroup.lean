import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

theorem omega_isPGroup {G : Type*} [Group G] {p : ℕ} (i : ℕ) (P : Subgroup G)
    (hP : IsPGroup p P) : IsPGroup p (Work.PGroup.omega p i P) :=
  hP.to_le (omega_le p i P)

end Work.PGroup
