import Mathlib.Algebra.Group.End

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.MulAut

/-- The underlying function of the monoid homomorphism `MulEquiv.toMonoidHom (MulAut.conj g)`
is conjugation by `g`: it sends `h` to `g * h * g⁻¹`. -/
theorem toMonoidHom_mulAut_conj_apply {G : Type*} [Group G] (g h : G) :
    (MulEquiv.toMonoidHom (MulAut.conj g)) h = g * h * g⁻¹ := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end Commons.GroupTheory.MulAut