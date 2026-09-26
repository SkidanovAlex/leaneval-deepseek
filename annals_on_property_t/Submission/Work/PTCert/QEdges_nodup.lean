import Mathlib
import Submission.Work.PTCert.QAdjOpDefs

namespace Work.PTCert

/-- The list `QEdges r` of edges `(i, j)` with `i < j < r` has no repeated entries:
it is built as a `flatMap`, over the (duplicate-free) list `List.range r` of first
coordinates `i`, of the injective image `j ↦ (i, j)` of the `j` with `i < j < r`, and two
rows with different first coordinates are disjoint. -/
theorem QEdges_nodup (r : ℕ) : (Submission.PTCert.QEdges r).Nodup := by
  unfold Submission.PTCert.QEdges
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · -- each row `i ↦ j ↦ (i, j)` is duplicate-free
    intro i _
    refine List.Nodup.filterMap ?_ List.nodup_range
    intro a a' b hb hb'
    simp only [Option.mem_def] at hb hb'
    split_ifs at hb hb'
    · simp only [Option.some.injEq] at hb hb'
      exact congrArg Prod.snd (hb.trans hb'.symm)
  · -- different rows are disjoint, since the first coordinate determines the row
    apply List.Pairwise.imp _ List.pairwise_lt_range
    intro a b hab
    show List.Disjoint _ _
    rw [List.disjoint_left]
    intro x hx hx'
    rw [List.mem_filterMap] at hx hx'
    obtain ⟨c, _, hxc⟩ := hx
    obtain ⟨d, _, hxd⟩ := hx'
    by_cases h1 : a < c
    · rw [if_pos h1, Option.some.injEq] at hxc
      by_cases h2 : b < d
      · rw [if_pos h2, Option.some.injEq] at hxd
        exact absurd (congrArg Prod.fst (hxc.trans hxd.symm)) (by omega)
      · rw [if_neg h2] at hxd; simp at hxd
    · rw [if_neg h1] at hxc; simp at hxc

end Work.PTCert
