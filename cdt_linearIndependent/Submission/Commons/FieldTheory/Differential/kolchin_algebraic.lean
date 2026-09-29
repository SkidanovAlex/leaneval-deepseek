import Mathlib
import Submission.Commons.FieldTheory.Differential.exists_deriv_of_deriv_eq_of_isAlgebraic

namespace Commons.FieldTheory.Differential

theorem kolchin_algebraic {R S : Type*} [Field R] [Differential R] [CharZero R] [Field S] [Algebra R S] [Differential S] [DifferentialAlgebra R S] {u : S} (hu : IsIntegral R u) {a : R} (ha : Differential.deriv u = algebraMap R S a) : ∃ b : R, Differential.deriv (u + algebraMap R S b) = 0 := by
  obtain ⟨g, hg⟩ := exists_deriv_of_deriv_eq_of_isAlgebraic (K := R) (L := S) ha hu.isAlgebraic
  refine ⟨-g, ?_⟩
  have hdg : Differential.deriv (-g) = -a := by rw [map_neg, hg]
  rw [map_add, ha, DifferentialAlgebra.deriv_algebraMap, hdg, map_neg, add_neg_cancel]

end Commons.FieldTheory.Differential
