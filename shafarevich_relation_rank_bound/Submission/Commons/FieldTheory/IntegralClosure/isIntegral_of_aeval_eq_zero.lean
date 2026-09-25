import Mathlib.RingTheory.Algebraic.Integral

namespace Commons.FieldTheory.IntegralClosure

lemma isIntegral_of_aeval_eq_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : Polynomial K} (hf : f ≠ 0) {β : L} (hβ : (Polynomial.aeval β) f = 0) :
    IsIntegral K β :=
  IsAlgebraic.isIntegral ⟨f, hf, hβ⟩

end Commons.FieldTheory.IntegralClosure