import Mathlib
import Submission.Work.Profiles.Basic
import Submission.Work.Profiles.Eta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Profiles

open MeasureTheory

open scoped ContDiff

/-- In the cusp region `r ≥ 3` the smoothing only ever samples `F` at points `≥ 11/4`,
where `F` agrees with `K e^t`.  Hence `prof F η r = K e^r ∫ e^{-t} η(t) dt`.

Note the hypotheses `hFc`, `hηcont`, `hηc` are not needed: the argument is purely
pointwise, using only the support condition `hηsupp` on `η`. -/
theorem prof_cusp {F η : ℝ → ℝ} (K : ℝ) (hF : ∀ t, 11/4 ≤ t → F t = K * Real.exp t)
    (hFc : Continuous F) (hηcont : Continuous η) (hηc : HasCompactSupport η)
    (hηsupp : ∀ t, 1/4 ≤ |t| → η t = 0) :
    ∀ r ≥ 3, prof F η r = K * (∫ t, Real.exp (-t) * η t) * Real.exp r := by
  intro r hr
  rw [prof]
  have hpt : ∀ t, F (r - t) * η t = (K * Real.exp r) * (Real.exp (-t) * η t) := by
    intro t
    by_cases h0 : η t = 0
    · rw [h0, mul_zero, mul_zero, mul_zero]
    · have hlt : |t| < 1/4 := by
        by_contra h
        exact h0 (hηsupp t (not_lt.mp h))
      have hrt : 11/4 ≤ r - t := by
        have h1 : t ≤ |t| := le_abs_self t
        linarith
      rw [hF (r - t) hrt, show r - t = r + (-t) from by ring, Real.exp_add]
      ring
  calc ∫ t, F (r - t) * η t
      = ∫ t, (K * Real.exp r) * (Real.exp (-t) * η t) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (K * Real.exp r) * ∫ t, Real.exp (-t) * η t := integral_const_mul _ _
    _ = K * (∫ t, Real.exp (-t) * η t) * Real.exp r := by ring

end Work.Profiles
