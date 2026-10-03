import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

namespace Work.KMTAreas.A7Hi2

/-- The chain term of the variational norm is invariant under *monotone reindexing* of the
sequence: the chain term of `i ↦ a (N i)` is at most the chain term of `a`.

Indeed both sides are suprema over the same family — a chain `(M 0, M 1, …, M J)` for the
composed sequence is the chain `(N (M 0), …, N (M J))` for `a` — and the second supremum ranges
over a *superset* of the index set of the first (`M ↦ N ∘ M` sends monotone maps to monotone
maps), so the inequality is immediate.  No subadditivity of `chainPart` is involved. -/
theorem chainPart_mono_comp (r : NNReal) (a : ℕ → ℂ) (N : ℕ → ℕ) (hN : Monotone N) :
    Work.KMTAreas.A7Hi.chainPart r (fun i : ℕ => a (N i)) ≤ Work.KMTAreas.A7Hi.chainPart r a := by
  unfold Work.KMTAreas.A7Hi.chainPart
  refine iSup_le (fun J => iSup_le (fun M => iSup_le (fun hM => ?_)))
  exact le_iSup_of_le J (le_iSup_of_le (N ∘ M) (le_iSup_of_le (hN.comp hM) le_rfl))

end Work.KMTAreas.A7Hi2
