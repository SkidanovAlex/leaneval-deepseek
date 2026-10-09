import Mathlib.RingTheory.Algebraic.Integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.IntegralClosure

lemma isIntegral_of_aeval_eq_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : Polynomial K} (hf : f ≠ 0) {β : L} (hβ : (Polynomial.aeval β) f = 0) :
    IsIntegral K β :=
  IsAlgebraic.isIntegral ⟨f, hf, hβ⟩

end Commons.FieldTheory.IntegralClosure