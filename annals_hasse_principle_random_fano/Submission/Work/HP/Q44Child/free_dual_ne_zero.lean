import Mathlib

namespace Work.HP.Q44Child

/-- Over `ℤ`, a free module is projective; hence the dual separates points:
a nonzero element admits a linear functional which does not vanish on it. -/
theorem free_dual_ne_zero {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M]
    {m : M} (hm : m ≠ 0) : ∃ f : M →ₗ[ℤ] ℤ, f m ≠ 0 :=
  Module.Projective.exists_dual_ne_zero ℤ hm

end Work.HP.Q44Child
