import Mathlib
import Submission.RSPsum_defs

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

lemma Qsum_small (t m : ℕ) (hm : m ≤ 2 ^ t) : Qsum (t + 1) m = Psum t m := by
  unfold Qsum Psum
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < 2 ^ t := lt_of_lt_of_le (Finset.mem_range.mp hk) hm
  rw [coeff_Q_extend t k hklt]

end RudinShapiro
end Submission
