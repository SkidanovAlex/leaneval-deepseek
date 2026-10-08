import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- `Ω₁` written with the general `omega` indexing at `i = 1` agrees with the dedicated
definition `omega1`: both are the closure of the set of elements `x` of `A` with `x ^ p = 1`. -/
theorem omega_one_eq_omega1 {G : Type*} [Group G] (p : ℕ) (A : Subgroup G) :
    Work.PGroup.omega p 1 A = Work.PGroup.omega1 G p A := by
  simp only [omega, omega1, pow_one]

end Work.PGroup
