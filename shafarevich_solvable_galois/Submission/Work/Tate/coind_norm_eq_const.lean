import Mathlib
import Submission.Work.Tate.CoindModule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- The norm of a function `f : G → R` with respect to the coinduced action
`(g • f) x = f (x * g)` is the constant function with value `∑ g, f g`.

Indeed, evaluating `N f = ∑ g, g • f` at `x` gives `∑ g, f (x * g)`, which is `∑ g, f g`
since left translation is a bijection of the finite group `G`. -/
theorem coind_norm_eq_const {G : Type*} [Group G] [Fintype G] {R : Type*} [AddCommGroup R]
    (f : G → R) :
    Work.Tate.norm G (G → R) f = Function.const G (∑ g : G, f g) := by
  funext x
  simp only [norm_apply, Function.const_apply, Finset.sum_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft x) (fun g => (g • f) x) (fun g => f g)
    (fun g => rfl)

end Work.Tate
