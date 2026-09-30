import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem finrank_ker_comp_of_surjective {K V U W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (e : V →ₗ[K] U) (g : U →ₗ[K] W) (he : Function.Surjective e)
    (hg : Function.Surjective g) :
    Module.finrank K (LinearMap.ker (g.comp e)) = Module.finrank K V - Module.finrank K W := by
  have hsurj : Function.Surjective (g.comp e) := hg.comp he
  have hrange : (g.comp e).range = ⊤ := LinearMap.range_eq_top_of_surjective _ hsurj
  have h1 := LinearMap.finrank_range_add_finrank_ker (g.comp e)
  rw [hrange, finrank_top] at h1
  omega

end Work.BW
