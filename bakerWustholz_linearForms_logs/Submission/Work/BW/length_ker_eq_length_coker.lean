import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For an endomorphism `f` of a module `T` of finite length, the length of the kernel equals the
length of the cokernel `T ⧸ f.range`. Route: the two short exact sequences
`0 → f.ker → T → f.range → 0` and `0 → f.range → T → T ⧸ f.range → 0`
(`LinearMap.exact_subtype_ker_map`, `LinearMap.exact_subtype_mkQ`) give
`length T = length f.ker + length f.range = length f.range + length (T ⧸ f.range)`; conclude by
cancelling `length f.range` (finite, being a submodule of `T`). -/
theorem length_ker_eq_length_coker {R T : Type*} [Ring R] [AddCommGroup T] [Module R T]
    (f : T →ₗ[R] T) (h : IsFiniteLength R T) :
    Module.length R f.ker = Module.length R (T ⧸ f.range) := by
  -- exactness of `0 → f.ker → T → f.range → 0`
  have hex : Function.Exact (f.ker).subtype f.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  -- length T = length f.ker + length f.range
  have h1 : Module.length R T = Module.length R f.ker + Module.length R f.range :=
    Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _)
      f.surjective_rangeRestrict hex
  -- length T = length f.range + length (T ⧸ f.range)
  have h2 : Module.length R T = Module.length R f.range + Module.length R (T ⧸ f.range) :=
    Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ f.range)
  -- `Module.length R f.range` is finite, so it can be cancelled
  have hne : Module.length R f.range ≠ ⊤ :=
    ne_top_of_le_ne_top (Module.length_ne_top_iff.mpr h)
      (Module.length_le_of_injective (Submodule.subtype _) (Submodule.subtype_injective _))
  have key := h1.symm.trans h2
  rw [add_comm (Module.length R f.ker) (Module.length R f.range)] at key
  exact WithTop.add_left_cancel hne key

end Work.BW
