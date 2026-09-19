import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.SpecialFunctions.Log

theorem log_one_add_ge7 (w : ℝ) (hw : 0 ≤ w) :
    w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4 + w ^ 5 / 5 - w ^ 6 / 6 + w ^ 7 / 7 - w ^ 8 / 8 ≤
      Real.log (1 + w) := by
  let P : ℝ → ℝ := fun x => x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 + x ^ 5 / 5 - x ^ 6 / 6 + x ^ 7 / 7 - x ^ 8 / 8
  let F : ℝ → ℝ := fun x => Real.log (1 + x) - P x
  have hA : ∀ y ∈ Set.Icc 0 w, HasDerivAt F (y ^ 8 / (1 + y)) y := by
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hyne : (1 : ℝ) + y ≠ 0 := by linarith
    have hlogy : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + y)) y := by
      have hid' : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 y := (hasDerivAt_id y).const_add (1 : ℝ)
      simpa using hid'.log hyne
    have h1 : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have hp2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
      simpa using (hasDerivAt_pow 2 y).div_const (2 : ℝ)
    have hp3 : HasDerivAt (fun t : ℝ => t ^ 3 / 3) (y ^ 2) y := by
      simpa using (hasDerivAt_pow 3 y).div_const (3 : ℝ)
    have hp4 : HasDerivAt (fun t : ℝ => t ^ 4 / 4) (y ^ 3) y := by
      simpa using (hasDerivAt_pow 4 y).div_const (4 : ℝ)
    have hp5 : HasDerivAt (fun t : ℝ => t ^ 5 / 5) (y ^ 4) y := by
      simpa using (hasDerivAt_pow 5 y).div_const (5 : ℝ)
    have hp6 : HasDerivAt (fun t : ℝ => t ^ 6 / 6) (y ^ 5) y := by
      simpa using (hasDerivAt_pow 6 y).div_const (6 : ℝ)
    have hp7 : HasDerivAt (fun t : ℝ => t ^ 7 / 7) (y ^ 6) y := by
      simpa using (hasDerivAt_pow 7 y).div_const (7 : ℝ)
    have hp8 : HasDerivAt (fun t : ℝ => t ^ 8 / 8) (y ^ 7) y := by
      simpa using (hasDerivAt_pow 8 y).div_const (8 : ℝ)
    have hPy : HasDerivAt
        ((((((((fun t : ℝ => t) - (fun t : ℝ => t ^ 2 / 2)) + (fun t : ℝ => t ^ 3 / 3)) -
          (fun t : ℝ => t ^ 4 / 4)) + (fun t : ℝ => t ^ 5 / 5)) - (fun t : ℝ => t ^ 6 / 6)) +
        (fun t : ℝ => t ^ 7 / 7)) - (fun t : ℝ => t ^ 8 / 8))
        (1 - y + y ^ 2 - y ^ 3 + y ^ 4 - y ^ 5 + y ^ 6 - y ^ 7) y := by
      simpa using ((((((((h1.sub hp2).add hp3).sub hp4).add hp5).sub hp6).add hp7).sub hp8))
    have hFy : HasDerivAt
        ((fun t : ℝ => Real.log (1 + t)) -
          ((((((((fun t : ℝ => t) - (fun t : ℝ => t ^ 2 / 2)) + (fun t : ℝ => t ^ 3 / 3)) -
            (fun t : ℝ => t ^ 4 / 4)) + (fun t : ℝ => t ^ 5 / 5)) - (fun t : ℝ => t ^ 6 / 6)) +
          (fun t : ℝ => t ^ 7 / 7)) - (fun t : ℝ => t ^ 8 / 8)))
        ((1 / (1 + y)) - (1 - y + y ^ 2 - y ^ 3 + y ^ 4 - y ^ 5 + y ^ 6 - y ^ 7)) y := by
      simpa using hlogy.sub hPy
    refine hFy.congr_deriv ?_
    field_simp [hyne]
    ring
  have hmono : MonotoneOn F (Set.Icc 0 w) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 w)
      (fun y hy ↦ (hA y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hA y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy' : y ∈ Set.Ioo 0 w := by simpa [interior_Icc] using hy
    have hy0 : 0 < y := hy'.1
    positivity
  have hF0 : F 0 = 0 := by simp [F, P]
  have h0in : (0 : ℝ) ∈ Set.Icc 0 w := by simpa using hw
  have hwin : w ∈ Set.Icc 0 w := by simpa using hw
  have hF0leFw : F 0 ≤ F w := hmono h0in hwin hw
  have hFw0 : 0 ≤ F w := by
    rw [← hF0]
    exact hF0leFw
  have hsub : 0 ≤ Real.log (1 + w) - P w := by simpa [F] using hFw0
  have hPle : P w ≤ Real.log (1 + w) := by linarith
  simpa [P] using hPle

end Commons.Analysis.SpecialFunctions.Log