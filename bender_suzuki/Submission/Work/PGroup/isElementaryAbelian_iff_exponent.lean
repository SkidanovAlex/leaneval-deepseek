import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- An elementary abelian `p`-subgroup is exactly a commutative subgroup whose exponent
divides `p`: the condition `∀ x : E, x ^ p = 1` is equivalent to `Monoid.exponent E ∣ p`. -/
theorem isElementaryAbelian_iff_exponent {G : Type*} [Group G] {p : ℕ} (E : Subgroup G) :
    Work.PGroup.IsElementaryAbelian p E ↔ IsMulCommutative E ∧ Monoid.exponent E ∣ p := by
  unfold Work.PGroup.IsElementaryAbelian
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]

end Work.PGroup
