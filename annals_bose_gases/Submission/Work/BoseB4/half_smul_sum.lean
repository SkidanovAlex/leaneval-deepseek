import Mathlib
import Submission.Work.BoseB4.SplitHbogPre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

lemma half_smul_sum {m : ℕ} [NeZero m] {ι : Type*} (s : Finset ι) (w : ι → ℝ) (c : ℝ)
    (v : ι → Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m))) :
    c • (∑ k ∈ s, w k • v k) = ∑ k ∈ s, ((c * w k : ℝ) : ℂ) • v k := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  rfl

end Work.BoseB4
