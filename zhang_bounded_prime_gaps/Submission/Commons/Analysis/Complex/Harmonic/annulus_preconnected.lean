import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Submission.Commons.Analysis.Calculus.hasDerivAt_integral_Ioi_of_continuous

namespace Commons.Analysis.Complex.Harmonic

/-- The open annulus `{z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}` (for `0 < r < R`) is
preconnected: it is the image under the complex exponential of the convex
vertical strip `{w | log r < w.re ∧ w.re < log R}`. -/
theorem annulus_preconnected {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    PreconnectedSpace {z : ℂ // r < ‖z‖ ∧ ‖z‖ < R} := by
  let A : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}
  let S : Set ℂ := {w : ℂ | Real.log r < w.re ∧ w.re < Real.log R}
  have hS_conv : Convex ℝ S := by
    rw [show S = {w : ℂ | Real.log r < w.re} ∩ {w : ℂ | w.re < Real.log R} by
      ext w
      simp [S]]
    exact (convex_halfSpace_re_gt (Real.log r)).inter (convex_halfSpace_re_lt (Real.log R))
  have hS_pre : IsPreconnected S := hS_conv.isPreconnected
  have hS_img : IsPreconnected (Complex.exp '' S) :=
    hS_pre.image Complex.exp Complex.continuousOn_exp
  have hA : A = Complex.exp '' S := by
    ext z
    constructor
    · intro hz
      have hz0 : z ≠ 0 := by
        intro hz0
        have : ‖z‖ ≠ 0 := ne_of_gt (lt_trans hr hz.1)
        rw [hz0] at this
        simp at this
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      change Real.log r < (Complex.log z).re ∧ (Complex.log z).re < Real.log R
      rw [Complex.log_re]
      exact ⟨Real.log_lt_log hr hz.1, Real.log_lt_log (hr.trans hz.1) hz.2⟩
    · rintro ⟨w, hw, rfl⟩
      have h1 : r < ‖Complex.exp w‖ := by
        rw [Complex.norm_exp]
        simpa [Real.exp_log hr] using (Real.exp_strictMono hw.1)
      have h2 : ‖Complex.exp w‖ < R := by
        rw [Complex.norm_exp]
        simpa [Real.exp_log (hr.trans hrR)] using (Real.exp_strictMono hw.2)
      exact ⟨h1, h2⟩
  have hA_pre : IsPreconnected A := by
    rw [hA]
    exact hS_img
  exact (isPreconnected_iff_preconnectedSpace (s := A)).mp hA_pre

end Commons.Analysis.Complex.Harmonic