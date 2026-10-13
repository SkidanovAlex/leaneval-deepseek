import Mathlib
import Submission.Work.WilE5.Pairwise
import Submission.Work.WilE5.SysL

namespace Work.WilE5.Pairwise

open WilkiesDesign WilkiesDesign.E
open Classical

/-- `uniqSets` on a cons unfolds into the head together with the (unfolded) recursive call. -/
theorem uniqSets_cons {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (rest : List (WilkiesDesign.E.Stratum p q)) :
    Work.WilE5.uniqSets (S :: rest) =
      S :: Work.WilE5.uniqSets
        (List.filter (fun T : WilkiesDesign.E.Stratum p q => decide (T.X.set ≠ S.X.set)) rest) := by
  rw [Work.WilE5.uniqSets.eq_def]

/-- `List.filter` on the `attach`ed list, then `unattach`, is `List.filter` on the original list. -/
theorem attach_filter_unattach {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (rest : List (WilkiesDesign.E.Stratum p q)) :
    (rest.attach.filter (fun x : {x // x ∈ rest} => decide (x.1.X.set ≠ S.X.set))).unattach =
      List.filter (fun T : WilkiesDesign.E.Stratum p q => decide (T.X.set ≠ S.X.set)) rest := by
  rw [List.unattach_filter
        (g := (fun T : WilkiesDesign.E.Stratum p q => decide (T.X.set ≠ S.X.set)))
        (hf := by intro x _; rfl),
      List.unattach_attach]

theorem uniqSetsSublist {p q : ℕ} (L : List (WilkiesDesign.E.Stratum p q)) :
    List.Sublist (Work.WilE5.uniqSets L) L := by
  induction L using uniqSets.induct with
  | case1 => simp [uniqSets]
  | case2 S rest ih =>
    rw [uniqSets_cons]
    refine List.Sublist.cons_cons S ?_
    rw [attach_filter_unattach] at ih
    exact ih.trans List.filter_sublist

end Work.WilE5.Pairwise
