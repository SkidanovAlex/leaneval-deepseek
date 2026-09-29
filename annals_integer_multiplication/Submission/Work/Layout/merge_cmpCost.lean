import Mathlib
import Submission.Work.Layout.MergeDefs
import Submission.Work.Layout.MergeTraceDefs
import Submission.Work.Layout.MergeRecsBounds

namespace Work.Layout

open HvdH Work.Layout

theorem merge_cmpCost (ks ls : List ℕ) (hnd : (ks ++ ls).Nodup) : cmpCost ks ls ≤ 20 * (((ks ++ ls).map (fun k => k.size + 2)).sum + ks.length + ls.length + 2) := by
  rw [Work.Layout.mergeRecs_cost]
  have hcol := Work.Layout.colSum_le ks ls hnd
  have hrow := Work.Layout.rowSum_le ks ls hnd
  have hsum : (((ks ++ ls).map (fun k => k.size + 2)).sum)
      = (ks.map (fun k => k.size)).sum + (ls.map (fun l => l.size)).sum
        + 2 * (ks.length + ls.length) := by
    rw [Work.Layout.sum_map_add_two, List.map_append, List.sum_append, List.length_append]
    try ring
  omega

end Work.Layout
