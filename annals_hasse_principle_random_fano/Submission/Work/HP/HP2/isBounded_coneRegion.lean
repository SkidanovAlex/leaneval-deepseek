import Mathlib
import Submission.Work.HP.PFDefs
import Submission.Work.HP.tau_basic

namespace Work.HP.HP2

/-- The cone region `coneRegion d n a α T = {x : ‖x‖ ≤ T, toR a ∈ Cgam (veronese d n x) α}` is
bounded: it is contained in the closed `rNorm`-ball of radius `max T 0` around the origin, because
`|x i| ≤ rNorm x ≤ T` for every coordinate `i`
(`Work.HP.abs_apply_le_rNorm`). -/
lemma isBounded_coneRegion (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α T : ℝ) :
    Bornology.IsBounded (Work.HP.coneRegion d n a α T) := by
  -- Membership in the cone region gives `rNorm x ≤ T ≤ max T 0`, hence `|x i| ≤ max T 0` for
  -- every coordinate; the sup-norm of `x` is therefore bounded by `max T 0`.
  refine Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : Fin (n + 1) → ℝ)) (r := max T 0)) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg (le_max_right T 0)]
  intro i
  rw [Real.norm_eq_abs]
  exact (Work.HP.abs_apply_le_rNorm x i).trans (hx.1.trans (le_max_left T 0))

end Work.HP.HP2
