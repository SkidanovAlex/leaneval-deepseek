/-
⚠ IMPORT-CLASH WORKAROUND (session 118).  Verbatim copy of the commons module
`gaussian_isoperimetric_blowup`, with its Ehrhard-route import re-routed to
`Submission.GaussIsoperimetricViaEhrhard` (which avoids the `toLp_norm_sq` clash between
`bobkov_strong_nD` and `brascamp_lieb_truncated`).  See that file for the full explanation.
-/
import Mathlib
import Submission.GaussIsoperimetricViaEhrhard

/-!
# The Gaussian isoperimetric inequality (blow-up / halfspace-threshold form)

This is the Sudakov–Tsirelson (1974) / Borell (1975) Gaussian isoperimetric
inequality, in the form used by Regev–Stephens-Davidowitz, *A reverse Minkowski
theorem*, Ann. of Math. 199 (2024): if a measurable set `U ⊆ ℝⁿ` has Gaussian mass
at least that of the half-line `(-∞, t]`, then its closed `ρ`-neighbourhood has
Gaussian mass at least that of `(-∞, t + ρ]`.

The proof is assembled on top of the shared commons development: the team proved
Ehrhard's inequality with one convex set
(`Commons.Analysis.GaussianMeasure.ehrhard_inequality_one_convex`), the asymptotic
behaviour of the Gaussian quantile of a large ball
(`...gaussian_ball_quantile_asymptotic`), and, combining them by the classical
Sudakov–Tsirelson scaling argument, the result
(`...gaussian_isoperimetric_via_ehrhard`), which is what this file records as the
requested lemma.

(The same statement is also available through the Bobkov functional-inequality
route developed in parallel in the commons.)
-/

namespace Commons.Analysis.GaussianMeasure

theorem gaussian_isoperimetric_blowup {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (t ρ : ℝ) (hρ : 0 ≤ ρ)
    (hUγ : (∫ x : ℝ in {x : ℝ | x ≤ t}, Real.exp (-Real.pi * x ^ 2)) ≤
            ∫ x in U, Real.exp (-Real.pi * ‖x‖ ^ 2)) :
    (∫ x : ℝ in {x : ℝ | x ≤ t + ρ}, Real.exp (-Real.pi * x ^ 2)) ≤
      ∫ x in {x : EuclideanSpace ℝ (Fin n) | ∃ u ∈ U, dist x u ≤ ρ},
        Real.exp (-Real.pi * ‖x‖ ^ 2) :=
  gaussian_isoperimetric_via_ehrhard U hU t ρ hρ hUγ

end Commons.Analysis.GaussianMeasure
