/-
# `radS α f` is `C³` on `(0,∞)` as soon as `L₁₂ f` is `C⁴` there

The radial profile of the `D_z`-defect of the transfer (`Transfer/Profiles.lean`) is

  `radS α f z = −(D_z a)(z)·L₁₂ f(z) − a(z)·z·(L₁₂ f)'(z) + (b'(z)/c)·L₁₂(Transport f)(0)`,

with the two elementary rational `z`-factors

  `a(z) = ampA α z = 2z/(c α·(1+z)²)`,  `b(z) = ampB α z = 2z²/(1+z)³`,
  `dAmpA α z = z·a'(z)`,  `dAmpB α z = z·b'(z)`.

Every factor is manifestly `C^∞` on `Ioi 0`: the two rational functions because their
denominators do not vanish there (`c α ≠ 0` follows from `Work.Spaces.c_bounds`, since
`1/10 ≤ c α`; and `1 + z > 0` for `z > 0`), the last summand because `z ↦ dAmpB α z / c α` is a
`div_const` of a smooth function and `L₁₂(Transport f)(0)` is a constant.  So the only analytic
input is that `L₁₂ f` be `C⁴` on the open half-line, whence its derivative is `C³` there
(`ContDiffOn.deriv_of_isOpen`), and `ContDiffOn` is closed under the products and sums at hand.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.AuxE2

theorem radS_contDiffOn_three (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ 4 (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (fun z => Work.FTS.CoercivityFix.Transfer.radS α f z) (Set.Ioi 0) := by
  -- `c α ≠ 0`, from `1/10 ≤ c α` (`Work.Spaces.c_bounds`)
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  -- the two rational `z`-factors are `C^∞` (hence `C⁴`) on `(0,∞)`
  have hampA : ContDiffOn ℝ 4 (ampA α) (Set.Ioi 0) := by
    change ContDiffOn ℝ 4 (fun z => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) (Set.Ioi 0)
    exact (((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_id).div
      ((contDiffOn_const (c := Work.Spaces.c α)).mul
        (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 2))
      (fun z hz => mul_ne_zero hc (pow_ne_zero 2 (by linarith [show (0 : ℝ) < z from hz]))))
  have hampB : ContDiffOn ℝ 4 (ampB α) (Set.Ioi 0) := by
    change ContDiffOn ℝ 4 (fun z => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi 0)
    exact (((contDiffOn_const (c := (2 : ℝ))).mul (contDiffOn_id.pow 2)).div
      (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 3)
      (fun z hz => pow_ne_zero 3 (by linarith [show (0 : ℝ) < z from hz])))
  -- hence their `z`-multiples `dAmpA α` and `dAmpB α / c α`, too
  have hdA : ContDiffOn ℝ 3 (dAmpA α) (Set.Ioi 0) := by
    change ContDiffOn ℝ 3 (fun z => z * deriv (ampA α) z) (Set.Ioi 0)
    exact contDiffOn_id.mul (hampA.deriv_of_isOpen isOpen_Ioi (by norm_num))
  have hdB : ContDiffOn ℝ 3 (fun z => dAmpB α z / Work.Spaces.c α) (Set.Ioi 0) := by
    change ContDiffOn ℝ 3 (fun z => z * deriv (ampB α) z / Work.Spaces.c α) (Set.Ioi 0)
    exact (contDiffOn_id.mul (hampB.deriv_of_isOpen isOpen_Ioi (by norm_num))).div_const _
  -- the analytic input: `L₁₂ f` is `C³` and its derivative is `C³`
  have hL : ContDiffOn ℝ 3 (Work.Coercivity.L12f f) (Set.Ioi 0) := hA.of_le (by norm_num)
  have hLd : ContDiffOn ℝ 3 (deriv (Work.Coercivity.L12f f)) (Set.Ioi 0) :=
    hA.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have key : ContDiffOn ℝ 3
      (fun z => -dAmpA α z * Work.Coercivity.L12f f z
        - ampA α z * (z * deriv (Work.Coercivity.L12f f) z)
        + (dAmpB α z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi 0) :=
    ((hdA.neg.mul hL).sub (hampA.of_le (by norm_num) |>.mul (contDiffOn_id.mul hLd))).add
      (hdB.mul contDiffOn_const)
  exact key.congr (fun z _ => by simp only [radS, dAmpA, dAmpB])

end Work.FTS.CoercivityFix.Transfer.AuxE2
