import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.isPSolvable_subgroup
import Submission.Work.Fitting.pLength_spec

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pLength_le_pLength_of_subgroup`

The `p`-length is monotone in the subgroup: if `G` is a finite `p`-solvable group and
`H ≤ G` is a `p`-solvable subgroup, then `pLength p H ≤ pLength p G`.

The mathematical content is that the upper `p`-series of `H` dominates the intersection of
`H` with the upper `p`-series of `G` (`comap_pCoreSeries_le`, from
`Work.Fitting.isPSolvable_subgroup`).  Since the upper `p`-series of `G` reaches `⊤` at some
index `n` (`G` is `p`-solvable), the series of `H` is `⊤` at that same index `n`; hence the
least index at which `H`'s series reaches `⊤` is at most `n`, and `pLength` is half of that
least index (for both groups).
-/

noncomputable section

open Classical

namespace Work.Fitting

variable {G : Type*} [Group G] [Finite G]

/-- If the upper `p`-series of `G` is `⊤` at `n`, so is that of any subgroup `H ≤ G`. -/
theorem pCoreSeries_eq_top_of_subgroup (p : ℕ) (H : Subgroup G) {n : ℕ}
    (hn : pCoreSeries p G n = ⊤) : pCoreSeries p H n = ⊤ := by
  have h1 := comap_pCoreSeries_le p G H n
  rw [hn, Subgroup.comap_top] at h1
  exact top_le_iff.mp h1

theorem pLength_le_pLength_of_subgroup (p : ℕ) (G : Type*) [Group G] [Finite G] (H : Subgroup G)
    [Work.Fitting.IsPSolvable p G] [Work.Fitting.IsPSolvable p H] :
    Work.Fitting.pLength p H ≤ Work.Fitting.pLength p G := by
  have hG : Work.Fitting.IsPSolvable p G := inferInstance
  have hH : Work.Fitting.IsPSolvable p H := inferInstance
  -- the least index at which the series of `H` reaches `⊤` is at most that of `G`
  have key : Nat.find hH.out ≤ Nat.find hG.out :=
    Nat.find_min' hH.out (pCoreSeries_eq_top_of_subgroup p H (Nat.find_spec hG.out))
  have hpLH : Work.Fitting.pLength p H = Nat.find hH.out / 2 := by
    unfold Work.Fitting.pLength
    rw [dite_eq_left hH]
  have hpLG : Work.Fitting.pLength p G = Nat.find hG.out / 2 := by
    unfold Work.Fitting.pLength
    rw [dite_eq_left hG]
  rw [hpLH, hpLG]
  exact Nat.div_le_div_right key

end Work.Fitting
