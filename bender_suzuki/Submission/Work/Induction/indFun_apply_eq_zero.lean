import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- Every summand of the defining sum of `indFun H φ g` is zero when no conjugate of `g` lies
-- in `H`, hence the sum is zero.
theorem indFun_apply_eq_zero {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ)
    (g : G) (h : ∀ x : G, x * g * x⁻¹ ∉ H) : Work.Induction.indFun H φ g = 0 :=
  indFun_apply_eq_zero_of_not_conj H φ g h

end Work.Induction
