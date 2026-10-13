/-
  WilE5 — turning a "no partial overlaps" list of strata into a pairwise disjoint one.

  The frozen statement requires the list `L` of strata to be pairwise disjoint, while the leaves
  produced by the recursion (within one sign cell) satisfy the weaker property

    any two leaves either are disjoint or have equal underlying sets

  (`Cells/leafDisj`).  Dropping, for each set that occurs, all but its first occurrence preserves
  the union (the dropped sets are *equal* to a kept one) and makes the list pairwise disjoint.
  This file sets up that filter; its properties are in `Pairwise/filterProps` and
  `Pairwise/uniqSetsSublist`.
-/
import Mathlib
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

/-- Drop from a list of strata every entry whose underlying set already occurred earlier. -/
def uniqSets {p q : ℕ} (L : List (Stratum p q)) : List (Stratum p q) :=
  match L with
  | [] => []
  | S :: rest => S :: uniqSets (rest.filter fun T => T.X.set ≠ S.X.set)
termination_by L.length
decreasing_by
  simp_wf
  calc (rest.attach.filter _).length ≤ rest.attach.length := List.length_filter_le _ _
    _ = rest.length := List.length_attach

end Work.WilE5
