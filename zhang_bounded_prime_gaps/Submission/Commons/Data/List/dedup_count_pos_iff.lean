import Mathlib.Data.List.Dedup
import Submission.Commons.Data.Int.mul_eq_pos_neg_parts

namespace Commons.Data.List

theorem dedup_count_pos_iff (l : List ℕ) (a : ℕ) :
    (0 < l.dedup.count a ↔ a ∈ l) ∧ (0 < l.dedup.count a ↔ 0 < l.count a) := by
  rw [List.count_pos_iff, List.mem_dedup]
  exact ⟨Iff.rfl, (List.count_pos_iff).symm⟩

end Commons.Data.List