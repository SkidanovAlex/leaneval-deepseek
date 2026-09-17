import Mathlib.LinearAlgebra.Basis.Basic

namespace Commons.LinearAlgebra.Basis

universe u

/-- Restricting a basis to a subtype of its index type yields linearly independent vectors. -/
theorem subtype_linearIndependent {R M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]
    {ι : Type u} (b : Module.Basis ι R M) (p : ι → Prop) :
    LinearIndependent R (fun a : {a : ι // p a} => b a.1) := by
  exact b.linearIndependent.comp Subtype.val (Subtype.val_injective)

end Commons.LinearAlgebra.Basis