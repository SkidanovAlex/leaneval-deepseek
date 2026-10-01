import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_aux
import Submission.Work.LinnikAreas.Density4.selU_floor_diff
import Submission.Work.LinnikAreas.Density4.selU_sub_eq_sum_Ico

namespace Work.LinnikAreas.Density4.Udecay

/-- **Abel summation for `selU`.**  The function `x ↦ selU x = Σ_{m ≤ x} μ(m) log(x/m)/m` is
constant on the interval `[⌊x⌋₊, ⌊x⌋₊ + 1)`, where it equals the log-weighted Möbius
reciprocal sum `logWeightedMuSum ⌊x⌋₊`; moving from `⌊x⌋₊` to `x` adds one further multiple of
the partial sums `muRecipSum ⌊x⌋₊ = Σ_{m ≤ ⌊x⌋₊} μ(m)/m` of the weights. -/
theorem selU_abel (x : ℝ) (hx : 1 ≤ x) :
    Work.LinnikAreas.Density4.selU x
      = Commons.NumberTheory.Moebius.logWeightedMuSum ⌊x⌋₊
        + Commons.NumberTheory.Moebius.muRecipSum ⌊x⌋₊ * (Real.log x - Real.log (⌊x⌋₊ : ℝ)) := by
  have hxpos : 0 < x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hNpos : (0 : ℝ) < (⌊x⌋₊ : ℕ) := by exact_mod_cast hN1
  have hdiff := selU_floor_diff x hx
  have hcast := selU_natCast_eq_logWeightedMuSum ⌊x⌋₊ hN1
  rw [hcast, Real.log_div (ne_of_gt hxpos) (ne_of_gt hNpos)] at hdiff
  linarith

end Work.LinnikAreas.Density4.Udecay
