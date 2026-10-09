import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

/-- The tensor product of two finite modules over a finite field is finite.

Since `X` and `T` are finite, they are finitely generated `K`-modules
(`Module.Finite.of_finite`), hence so is `X ⊗[K] T` (`Module.Finite.tensorProduct`),
and a finitely generated module over a finite ring is finite
(`Module.finite_of_finite`). -/
theorem finite_tensorProduct_of_finite (K : Type) [Field K] [Finite K] (X T : Type)
    [AddCommGroup X] [Module K X] [Finite X] [AddCommGroup T] [Module K T] [Finite T] :
    Finite (TensorProduct K X T) := by
  have hX : Module.Finite K X := Module.Finite.of_finite
  have hT : Module.Finite K T := Module.Finite.of_finite
  have hXT : Module.Finite K (TensorProduct K X T) := Module.Finite.tensorProduct K X T
  exact Module.finite_of_finite K

end Work.Shrinking
