import Mathlib.RingTheory.Norm.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Norm

lemma norm_map_algEquiv {F E E' : Type*} [Field F] [Field E] [Field E'] [Algebra F E] [Algebra F E']
    [Module.Finite F E] [Module.Finite F E'] (σ : E ≃ₐ[F] E') (x : E) :
    Algebra.norm F (σ x) = Algebra.norm F x := by
  exact Algebra.norm_eq_of_algEquiv σ x

end Commons.FieldTheory.Norm
