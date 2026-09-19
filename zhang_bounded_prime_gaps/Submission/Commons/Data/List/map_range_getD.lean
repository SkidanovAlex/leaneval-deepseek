import Mathlib.Data.List.GetD
import Submission.Commons.Data.List.dedup_count_pos_iff

namespace Commons.Data.List

theorem map_range_getD {α M : Type*} (l : List α) (d : α) (f : α → M) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < l.length := by rwa [List.length_map] at h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range (by simpa using h1),
        List.getD_eq_getElem l d hi]

end Commons.Data.List