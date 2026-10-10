import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.CoindModule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- A function `f : G → R` is fixed by the coinduced action of `G` on `G → R` if and only if it
is constant.  Indeed `(g • f) x = f (x * g)`, so `g • f = f` for all `g` means that `f` is
invariant under right multiplication, and for a group this is exactly constancy. -/
theorem coind_fixed_iff_const {G : Type*} [Group G] {R : Type*} [AddCommGroup R]
    (f : G → R) :
    f ∈ Work.Tate.fixedSubgroup G (G → R) ↔ ∃ c : R, f = Function.const G c := by
  constructor
  · intro hf
    refine ⟨f 1, ?_⟩
    funext y
    have h2 : ((1⁻¹ * y) • f) 1 = f 1 := congrFun (hf (1⁻¹ * y)) 1
    rw [coind_smul_eq] at h2
    simpa using h2
  · rintro ⟨c, rfl⟩ g
    funext x
    rw [coind_smul_eq]
    rfl

end Work.Tate
