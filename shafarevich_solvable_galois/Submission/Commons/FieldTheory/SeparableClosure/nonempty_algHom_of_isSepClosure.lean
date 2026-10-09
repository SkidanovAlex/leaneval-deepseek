import Mathlib.FieldTheory.IsSepClosed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.SeparableClosure

/-- Any finite separable extension `F'` of `F` embeds into a separable closure `E` of `F`:
the (random) `F`-algebra homomorphism `IsSepClosed.lift` is such an embedding. -/
theorem nonempty_algHom_of_isSepClosure {F F' E : Type*} [Field F] [Field F'] [Field E]
    [Algebra F F'] [Algebra F E] [IsSepClosure F E] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] : Nonempty (F' →ₐ[F] E) := by
  haveI : IsSepClosed E := IsSepClosure.sep_closed F
  exact ⟨IsSepClosed.lift⟩

end Commons.FieldTheory.SeparableClosure