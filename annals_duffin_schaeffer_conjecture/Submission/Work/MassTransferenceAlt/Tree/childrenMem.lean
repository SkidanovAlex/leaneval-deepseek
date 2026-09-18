import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data

namespace Work.MassTransferenceAlt.Tree

/-- Every ball of the construction has at least one child. -/
lemma childrenMem (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : Work.MassTransferenceAlt.TreeData d c ρ η)
    {n : ℕ} {B : ℕ} (hB : B ∈ T.lev n) :
    ∃ i ∈ T.lev (n+1), T.par (n+1) i = some B := by
  classical
  -- the local level of `B` has `nsub d (ρ B)` sub-levels, all of them non-empty
  have hnon : ∀ k, k < Work.MassTransferenceAlt.nsub d (ρ B) →
      ∃ i ∈ (T.lev (n+1)).filter (fun i => T.par (n+1) i = some B), T.sub (n+1) i = k :=
    (T.loc n B hB).2.2.2.2.2.2.1
  obtain ⟨i, hi, _⟩ := hnon 0 (lt_of_lt_of_le Nat.zero_lt_one
    (Work.MassTransferenceAlt.nsub_pos d (ρ B)))
  exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

end Work.MassTransferenceAlt.Tree
