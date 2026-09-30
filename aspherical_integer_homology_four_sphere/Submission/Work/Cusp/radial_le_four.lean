import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.collarHeight_mem
import Submission.Work.Cusp.nrm_le_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The metric radial coordinate of the filling stays below the top of the collar.**

`radial v p y` is `2 r_J ‖p‖∞` in the inner region (`‖p‖∞ ≤ 1/2`) and `R₀ − log (collarS v p y)`
in the collar (`‖p‖∞ > 1/2`).  On the source `1/24 < ‖p‖∞ ≤ 1`:

* inner region: `‖p‖∞ ≤ 1/2` gives `2 r_J ‖p‖∞ ≤ r_J = 3 < r_J + 1`;
* collar: `‖p‖∞ ∈ (1/2, 1]` and `β (cuspX v (u p) y) ∈ [βMin, βMax]`, so
  `collarHeight_mem` gives `collarS v p y = collarHeight ‖p‖∞ β > s₁ = 11/10 > 1`, whence
  `log (collarS v p y) > 0` and `radial = R₀ − log (collarS v p y) < R₀ = 7/2 < 4 = r_J + 1`. -/
theorem radial_le_four (v : Fin 5) (p y : E2) (hp : p ∈ Sq) (h : 1/24 < nrm p) :
    radial v p y < rJ + 1 := by
  rw [radial]
  split_ifs with hc
  · -- inner region: `radial = 2 r_J ‖p‖∞ ≤ r_J`
    rw [rJ]
    nlinarith
  · -- collar: `radial = R₀ − log (collarS v p y)`, and the logarithm is positive
    have hc' : 1 / 2 ≤ nrm p := le_of_lt (not_le.mp hc)
    have ht1 : nrm p ≤ 1 := nrm_le_one hp
    have hmem := collarHeight_mem (nrm p) (beta (cuspX v (u p) y)) hc' ht1
      (beta_min_le _) (beta_le_max _)
    have hs1 : (1 : ℝ) < s1 := by rw [s1]; norm_num
    have h1 : (1 : ℝ) < collarS v p y := lt_trans hs1 hmem.1
    have hlog : 0 < Real.log (collarS v p y) := Real.log_pos h1
    rw [rJ, R0]
    linarith

end Work.Cusp
