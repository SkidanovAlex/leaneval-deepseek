import Mathlib
import Submission.Work.TMComp.Kotani.ell_defect_le
import Submission.Work.TMComp.Kotani.L6_algebra
import Submission.Work.TMComp.Kotani.Objects

namespace Work.TMComp.LocCantor

open Work.TMComp.Kotani

/-- The imaginary part of `E / 2` (division by the complex number `2`). -/
private lemma im_div_two (E : ℂ) : (E / 2).im = E.im / 2 := by
  rw [Complex.div_im]; simp; ring

/-- The imaginary part of `star E / 2`. -/
private lemma im_star_div_two (E : ℂ) : (star E / 2).im = -(E.im / 2) := by
  rw [Complex.div_im]; simp; ring

theorem K2_pointwise_eq (α lam : ℝ) (y : ℝ) {E : ℂ} (hE : 0 < E.im) :
    1 / Work.TMComp.Kotani.N1 α lam E y + 1 / Work.TMComp.Kotani.N2 α lam E y
        - 4 * (-1 / Work.TMComp.Kotani.defect α lam E y).im
      = (Work.TMComp.Kotani.defect α lam E y).im
          * ‖(Work.TMComp.Kotani.mfun α lam E y - E / 2)
              - (Work.TMComp.Kotani.sigSec α lam E y - star E / 2)‖ ^ 2
          / (Work.TMComp.Kotani.N1 α lam E y * Work.TMComp.Kotani.N2 α lam E y
              * ‖Work.TMComp.Kotani.defect α lam E y‖ ^ 2) := by
  -- The imaginary parts of `m - E/2` and `σ - star E/2` are exactly `N₁` and `N₂`.
  have ha_im : (mfun α lam E y - E / 2).im = N1 α lam E y := by
    rw [Complex.sub_im, im_div_two, N1]
  have hc_im : (sigSec α lam E y - star E / 2).im = N2 α lam E y := by
    rw [Complex.sub_im, im_star_div_two, N2]; ring
  -- `(m - E/2) - star (σ - star E/2) = m - s = defect`.
  have hdef : (mfun α lam E y - E / 2) - star (sigSec α lam E y - star E / 2)
      = defect α lam E y := by
    rw [star_sub, star_div₀, star_star]
    rw [defect, ← conj_sigSec]
    simp
  -- (L6) with `a := m - E/2`, `c := σ - star E/2`.
  have hL6 := L6_algebra (mfun α lam E y - E / 2) (sigSec α lam E y - star E / 2)
    (by rw [ha_im]; exact N1_pos α lam E hE y)
    (by rw [hc_im]; exact N2_pos α lam E hE y)
  rw [ha_im, hc_im, hdef] at hL6
  exact hL6

end Work.TMComp.LocCantor
