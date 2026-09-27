import Mathlib
import Submission.Work.Mostow.BdExt.qiRayStep

/-!
# Comparing directions at comparable levels

`norm_sub_dirv_le_sqrt` (in `qiRayStep`) bounds the chord between the Euclidean directions of two
nonzero points by

  `sqrt (2 (cosh D - 1) / (sinh (lvl u) * sinh (lvl v)))`

as soon as the two points are at hyperbolic distance at most `D`.  If both levels are at least a
common `L ≥ 1`, the denominator can be replaced by the smaller constant `sinh L · sinh L`, which
gives the uniform estimate proved here:

  `‖dirv u - dirv v‖ ≤ sqrt (2 (cosh M - 1)) / sinh L`.

This is the form in which the estimate is consumed by the Morse/boundary-extension argument: the
right-hand side no longer depends on `u`, `v` individually but only on the distance bound `M` and
the level bound `L`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- Division by a larger (nonnegative) denominator only decreases a nonnegative quotient:
the analytic step of the comparison, with the `sinh` monotonicity already applied. -/
lemma sqrt_div_le_sqrt_div_sinh (A a b L : ℝ) (hA : 0 ≤ A)
    (hprod : Real.sinh L * Real.sinh L ≤ Real.sinh a * Real.sinh b)
    (hLpos : 0 < Real.sinh L) :
    Real.sqrt (A / (Real.sinh a * Real.sinh b)) ≤ Real.sqrt A / Real.sinh L := by
  have hden : 0 < Real.sinh L * Real.sinh L := mul_pos hLpos hLpos
  have hdiv : A / (Real.sinh a * Real.sinh b) ≤ A / (Real.sinh L * Real.sinh L) :=
    div_le_div_of_nonneg_left hA hden hprod
  refine le_trans (Real.sqrt_le_sqrt hdiv) ?_
  rw [Real.sqrt_div hA, Real.sqrt_mul_self (le_of_lt hLpos)]

/-- **The direction comparison.**  Two nonzero points at hyperbolic distance at most `M` whose
levels are both at least `L ≥ 1` have Euclidean directions (as seen from the chart origin) at
distance at most `sqrt (2 (cosh M - 1)) / sinh L`. -/
theorem bdDirvCmp (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n) (u v : Submission.Mostow.E n)
    (hu : u ≠ 0) (hv : v ≠ 0) (M L : ℝ) (hM : 0 ≤ M)
    (hd : Submission.Mostow.hdist u v ≤ M) (hL : 1 ≤ L)
    (huL : L ≤ Work.Mostow.BdExt.lvl u) (hvL : L ≤ Work.Mostow.BdExt.lvl v) :
    ‖Work.Mostow.BdExt.dirv u - Work.Mostow.BdExt.dirv v‖ ≤
      Real.sqrt (2 * (Real.cosh M - 1)) / Real.sinh L := by
  have hbound := norm_sub_dirv_le_sqrt hI hu hv M hM hd
  refine le_trans hbound ?_
  have hA : (0 : ℝ) ≤ 2 * (Real.cosh M - 1) := by
    have := Real.one_le_cosh M
    linarith
  have hLpos : 0 < Real.sinh L := Real.sinh_pos_iff.mpr (by linarith)
  have hapos : 0 < Real.sinh (lvl u) := Real.sinh_pos_iff.mpr (lvl_pos u hu)
  have hmono1 : Real.sinh L ≤ Real.sinh (lvl u) := Real.sinh_le_sinh.mpr huL
  have hmono2 : Real.sinh L ≤ Real.sinh (lvl v) := Real.sinh_le_sinh.mpr hvL
  have hprod : Real.sinh L * Real.sinh L ≤ Real.sinh (lvl u) * Real.sinh (lvl v) :=
    mul_le_mul hmono1 hmono2 (le_of_lt hLpos) (le_of_lt hapos)
  exact sqrt_div_le_sqrt_div_sinh _ _ _ _ hA hprod hLpos

end

end Work.Mostow.BdExt
