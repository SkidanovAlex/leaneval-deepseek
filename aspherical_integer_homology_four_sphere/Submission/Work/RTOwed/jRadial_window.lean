import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.radial_bounds
import Submission.Work.Cusp.radial_half
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.nrm_le_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The radial window of the junction charts

For a point `p` of the filling square `Sq` with `‖p‖∞ ≥ 1/2` — i.e. anywhere in the collar layer,
including the junction `‖p‖∞ = 1/2` — the metric radial coordinate `Work.Cusp.radial v p y` of the
filling of the `v`-th cusp lies in the open window `(1/2, rBig)` with `rBig = 17/5`.

On the whole collar `1/2 ≤ ‖p‖∞` the radial coordinate is the UHS value `R₀ − log (collarS v p y)`
(`Work.Cusp.radial_collar`), and for `p ∈ Sq` the layer parameter is `t = ‖p‖∞ ∈ [1/2, 1]` while the
ceiling is `b = β (cuspX v (u p) y) ∈ [√(3/2), 3/2]`.  Hence, writing the logarithm of the collar
height out (`log s_J = 1/2`),

`log (collarS v p y) = (2t−1) log b + (1−t)`.

Both sides of this expression are pinned by purely rational bounds on `log b`:

* `log b ≤ log (3/2) ≤ 3/2 − 1 = 1/2` (`Real.log_le_sub_one_of_pos`), so with `2t−1 ≥ 0`
  `log (collarS) ≤ (2t−1)/2 + (1−t) = 1/2`, giving `radial ≥ R₀ − 1/2 = 3 > 1/2`;
* `log b ≥ log β_min = log (3/2)/2 ≥ 1/6` (since `log (3/2) = −log (2/3) ≥ 1 − 2/3 = 1/3`), so with
  `2t−1 ≥ 0` and `t ≤ 1`, `log (collarS) ≥ (2t−1)/6 + (1−t) = (5−4t)/6 ≥ 1/6`, giving
  `radial ≤ R₀ − 1/6 = 10/3 < 17/5 = rBig`.

This is the radial-window statement used by the junction charts: their `r`-source `(1/4, rBig)`
contains the whole collar layer `[rJ, R₀ − log β_min]`.
-/

namespace Work.RTOwed

open Work.Cusp

theorem jRadial_window (v : Work.Space.Cusp) (p y : Work.Cusp.E2) (hp : p ∈ Work.Cusp.Sq)
    (h1 : 1 / 2 ≤ Work.Cusp.nrm p) :
    1 / 2 < Work.Cusp.radial v p y ∧ Work.Cusp.radial v p y < Work.RTOwed.rBig := by
  -- the layer parameter is at most `1` on the square
  have ht1 : nrm p ≤ 1 := nrm_le_one hp
  -- rational bounds for `log (β (cuspX v (u p) y))`
  have hbpos : 0 < beta (cuspX v (u p) y) := beta_pos _
  have hble : beta (cuspX v (u p) y) ≤ 3 / 2 := by
    simpa [betaMax] using beta_le_max (cuspX v (u p) y)
  have hbge : betaMin ≤ beta (cuspX v (u p) y) := beta_min_le _
  have hlogble : Real.log (beta (cuspX v (u p) y)) ≤ 1 / 2 := by
    calc Real.log (beta (cuspX v (u p) y))
        ≤ beta (cuspX v (u p) y) - 1 := Real.log_le_sub_one_of_pos hbpos
      _ ≤ 3 / 2 - 1 := by linarith
      _ = 1 / 2 := by norm_num
  have hlogbge : 1 / 6 ≤ Real.log (beta (cuspX v (u p) y)) := by
    have hmono : Real.log betaMin ≤ Real.log (beta (cuspX v (u p) y)) :=
      Real.log_le_log (by rw [betaMin]; positivity) hbge
    have hsqrt : Real.log betaMin = Real.log (3 / 2) / 2 := by
      rw [betaMin, Real.log_sqrt (by norm_num)]
    have h32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
      have hinv : Real.log (2 / 3) = -Real.log (3 / 2) := by
        have hi := Real.log_inv (3 / 2)
        rw [show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num] at hi
        exact hi
      linarith
    rw [hsqrt] at hmono
    linarith
  -- the collar identity, written in terms of `t = ‖p‖∞`
  have hlogS : Real.log (collarS v p y)
      = (2 * nrm p - 1) * Real.log (beta (cuspX v (u p) y)) + (1 - nrm p) := by
    rw [collarS, collarHeight, Real.log_exp, log_sJ]
    ring
  have h2t : 0 ≤ 2 * nrm p - 1 := by linarith
  have hup : (2 * nrm p - 1) * Real.log (beta (cuspX v (u p) y)) + (1 - nrm p) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hlogble h2t
    linarith
  have hlo : 1 / 6 ≤ (2 * nrm p - 1) * Real.log (beta (cuspX v (u p) y)) + (1 - nrm p) := by
    have hm := mul_le_mul_of_nonneg_left hlogbge h2t
    linarith
  rw [radial_collar v p y h1, hlogS]
  unfold Work.Cusp.R0 Work.RTOwed.rBig
  constructor <;> linarith

end Work.RTOwed
