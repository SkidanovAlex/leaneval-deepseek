import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.fill.tendsto_tail_piFinset_wt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

theorem tendsto_tail_piFinset_wt {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (hs : Fintype.card ι < 2 * s) :
    Filter.Tendsto
      (fun N : ℕ => ∑' k : {k : ι → ℤ // k ∉ Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ)) (N : ℤ))},
        ((Work.Diff.STE.wt k.1) ^ s)⁻¹)
      Filter.atTop (nhds 0) :=
  Work.Diff.STE.fill.tendsto_tail_piFinset_wt s hs

end Work.Diff.STE
