import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.ballConvexAux
import Submission.Work.Mostow.comboLeMax
import Submission.Work.Mostow.tpartSegfun

/-!
# Convexity of hyperbolic balls: the segment between two points stays in the larger ball

In the hyperboloid model the point of the geodesic from `p` to `q` at distance `s` from `p` has
lift the Minkowski-linear combination
`hlift (segfun p q s) = (sinh (d-s)/sinh d) • hlift p + (sinh s/sinh d) • hlift q`, `d = hdist p q`.
Since the Minkowski pairing of `hlift A` with a point is (minus) the cosh of its distance from
`A`, the quantity `cosh (hdist A ·)` is affine along the segment:
`cosh (hdist A (segfun p q s)) = a·cosh (hdist A p) + b·cosh (hdist A q)` with `a, b ≥ 0`,
`a + b ≤ 1`. Hence it is at most the maximum of the two endpoint values, and monotonicity of
`cosh` on `[0,∞)` gives `hdist A (segfun p q s) ≤ max (hdist A p) (hdist A q)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem ballConvex {n : ℕ} (p q A : E n) (hpq : p ≠ q) (s : ℝ) (hs : s ∈ Set.Icc 0 (hdist p q)) :
    hdist A (segfun p q s) ≤ max (hdist A p) (hdist A q) := by
  have hspos : 0 < Real.sinh (hdist p q) := Real.sinh_pos_iff.mpr (hdistPosOfNe hpq)
  have hsd : Real.sinh (hdist p q) ≠ 0 := ne_of_gt hspos
  -- the two endpoint values of `cosh (hdist A ·)`
  set Mp := tpart A * tpart p - inner ℝ A p with hMp
  set Mq := tpart A * tpart q - inner ℝ A q with hMq
  -- the affine coefficients of the segment
  set a := Real.sinh (hdist p q - s) / Real.sinh (hdist p q) with ha
  set b := Real.sinh s / Real.sinh (hdist p q) with hb
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith [hs.2])) (le_of_lt hspos)
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hs.1) (le_of_lt hspos)
  have hab : a + b ≤ 1 := by
    rw [ha, hb, ← add_div, div_le_one hspos]
    exact sinhSegLe hs
  have hMp0 : 0 ≤ Mp := by
    rw [hMp]; linarith [one_le_cosh_hdist A p]
  have hMq0 : 0 ≤ Mq := by
    rw [hMq]; linarith [one_le_cosh_hdist A q]
  -- affinity of `cosh (hdist A ·)` along the segment
  have hcd : tpart A * tpart (segfun p q s) - inner ℝ A (segfun p q s) = a * Mp + b * Mq := by
    rw [ha, hb, hMp, hMq, tpartSegfun p q s hsd hs, segfun, inner_add_right, inner_smul_right,
      inner_smul_right]
    ring
  have hcast : Real.cosh (hdist A (segfun p q s)) =
      tpart A * tpart (segfun p q s) - inner ℝ A (segfun p q s) := cosh_hdist A _
  have hR : max Mp Mq = Real.cosh (max (hdist A p) (hdist A q)) := by
    rw [hMp, hMq, ← cosh_hdist A p, ← cosh_hdist A q,
      coshMax (hdist_nonneg A p) (hdist_nonneg A q)]
  have hbound : Real.cosh (hdist A (segfun p q s)) ≤
      Real.cosh (max (hdist A p) (hdist A q)) := by
    rw [hcast, hcd, ← hR]
    exact comboLeMax ha0 hb0 hab hMp0 hMq0
  have h := Real.cosh_le_cosh.mp hbound
  rwa [abs_of_nonneg (hdist_nonneg A _),
    abs_of_nonneg (le_trans (hdist_nonneg A p) (le_max_left _ _))] at h

end Work.Mostow
