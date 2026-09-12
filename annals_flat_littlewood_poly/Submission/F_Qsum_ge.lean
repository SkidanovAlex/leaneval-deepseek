import Mathlib
import Submission.RSPsum_defs

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

lemma Qsum_ge (t m : ℕ) (hm : 2 ^ t ≤ m) : Qsum t m = Q t := by
  rw [Qsum]
  symm
  exact (Q t).as_sum_range_C_mul_X_pow' (n := m) (by
    calc
      (Q t).natDegree ≤ 2 ^ t - 1 := Q_natDegree_le t
      _ < m := by
        have h1 : 1 ≤ 2 ^ t := two_pow_ge_one t
        omega)

end RudinShapiro
end Submission
