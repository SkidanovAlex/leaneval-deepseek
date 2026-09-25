import Mathlib
import Submission.Work.QuadraticFields.MultiquadraticInside

namespace Work.QuadraticFields

theorem finiteDimensional_adjoin_sqrt {M : Type*} [Field M] [Algebra ℚ M] (a : ℚ) (x : M)
    (hx : x ^ 2 = algebraMap ℚ M a) :
    FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ ({x} : Set M)) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hx]; exact isIntegral_algebraMap)

end Work.QuadraticFields
