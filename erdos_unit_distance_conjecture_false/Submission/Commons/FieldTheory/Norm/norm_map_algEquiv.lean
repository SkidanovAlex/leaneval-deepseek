import Mathlib.RingTheory.Norm.Basic

namespace Commons.FieldTheory.Norm

lemma norm_map_algEquiv {F E E' : Type*} [Field F] [Field E] [Field E'] [Algebra F E] [Algebra F E']
    [Module.Finite F E] [Module.Finite F E'] (σ : E ≃ₐ[F] E') (x : E) :
    Algebra.norm F (σ x) = Algebra.norm F x := by
  exact Algebra.norm_eq_of_algEquiv σ x

end Commons.FieldTheory.Norm
