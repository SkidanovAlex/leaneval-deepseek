import Mathlib
import Submission.Work.Mostow.nearId_blk

/-!
# Monotonicity of the `fermiW` distance in the base point

For `fermiW 1 m v W = (√(1+‖W‖²)·v, W)` in the chart `E (1+m)`, the hyperbolic-cosine formula
(`nib_cosh_hdist_fermiW`) reads

  cosh d(fermiW v W, fermiW v' W') = √(1+‖W‖²)·√(1+‖W'‖²)·cosh d(v, v') − ⟪W, W'⟫ .

Since `cosh d(v,v) = 1 ≤ cosh d(v',v)`, replacing the tangential (foot) coordinate `v` by `v'` can only
*increase* the distance between the two points with normal coordinates `W` and `W'`.  This file records
that monotonicity in the exact form requested.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem nib_hdist_fermiW_le (m : ℕ) (v v' : Submission.Mostow.E 1) (W W' : Submission.Mostow.E m) :
    Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W) (Submission.Mostow.fermiW 1 m v W')
      ≤ Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v' W') (Submission.Mostow.fermiW 1 m v W) := by
  -- `cosh` is strictly increasing on `[0, ∞)`, so it suffices to compare the two cosines.
  have hcosh : Real.cosh (hdist (fermiW 1 m v W) (fermiW 1 m v W'))
      ≤ Real.cosh (hdist (fermiW 1 m v' W') (fermiW 1 m v W)) := by
    rw [nib_cosh_hdist_fermiW, nib_cosh_hdist_fermiW]
    -- the left pair has the same foot `v`, so `cosh (hdist v v) = 1`
    rw [nib_hdist_self, Real.cosh_zero, mul_one]
    have hS : 0 ≤ √(1 + ‖W‖ ^ 2) * √(1 + ‖W'‖ ^ 2) := by positivity
    have h2 : 1 ≤ Real.cosh (hdist v' v) := Real.one_le_cosh _
    have hmain : √(1 + ‖W‖ ^ 2) * √(1 + ‖W'‖ ^ 2)
        ≤ √(1 + ‖W'‖ ^ 2) * √(1 + ‖W‖ ^ 2) * Real.cosh (hdist v' v) := by
      rw [mul_comm (√(1 + ‖W'‖ ^ 2)) (√(1 + ‖W‖ ^ 2))]
      calc √(1 + ‖W‖ ^ 2) * √(1 + ‖W'‖ ^ 2)
          = √(1 + ‖W‖ ^ 2) * √(1 + ‖W'‖ ^ 2) * 1 := by ring
        _ ≤ √(1 + ‖W‖ ^ 2) * √(1 + ‖W'‖ ^ 2) * Real.cosh (hdist v' v) :=
            mul_le_mul_of_nonneg_left h2 hS
    rw [real_inner_comm W W']
    linarith
  have h := Real.cosh_le_cosh.mp hcosh
  rwa [abs_of_nonneg (nib_hdist_nonneg _ _), abs_of_nonneg (nib_hdist_nonneg _ _)] at h

end Work.Mostow
