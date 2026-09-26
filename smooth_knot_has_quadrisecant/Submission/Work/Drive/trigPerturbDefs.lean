import Mathlib
import Submission.Work.Drive.curvatureAPI

/-!
# Definitions for the trigonometric perturbation brick

For a finite set `S` of parameters in `[0, period)` this file defines an explicit analytic
`period`-periodic curve `pertCurve S B` whose velocity vanishes at every point of `S` and whose
acceleration at `i ∈ S` is a *nonzero* multiple of the prescribed vector `B i`.

The construction is a product of two factors:

* `pertWeight S` is the scalar weight `∏_{j ∈ S} (1 - cos (t - j))`, which has a double zero at
  every `j ∈ S` (value `0` and first derivative `0`), with nonvanishing second derivative there;
* `pertField S B` is the `Space`-valued interpolant `t ↦ Σ_{j ∈ S} η_j(t) • B j` built from the
  Lagrange-type weights `pertEta S j`, which satisfy `η_j(i) = 1` if `i = j` and `η_j(i) = 0`
  for `i ∈ S`, `i ≠ j` (so that `pertField S B i = B i` for `i ∈ S`).

Then `pertCurve S B = pertWeight S • pertField S B` has, at `i ∈ S`,
`deriv (pertCurve S B) i = 0` and
`deriv (deriv (pertCurve S B)) i = (∏_{l ∈ S.erase i} (1 - cos (i - l))) • B i`,
the scalar being nonzero because distinct points of `S` are distinct modulo `2π`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- Scalar weight with a double zero at every point of `S`:
`pertWeight S t = ∏_{j ∈ S} (1 - cos (t - j))`. -/
noncomputable def pertWeight (S : Finset ℝ) (t : ℝ) : ℝ :=
  ∏ j ∈ S, (1 - Real.cos (t - j))

/-- Lagrange-type interpolation weight of the parameter `j` inside `S`:
its value is `1` at `j` and `0` at every other point of `S`. -/
noncomputable def pertEta (S : Finset ℝ) (j : ℝ) (t : ℝ) : ℝ :=
  ∏ l ∈ S.erase j, ((Real.cos (t - j) - Real.cos (l - j)) / (1 - Real.cos (l - j)))

/-- The `Space`-valued interpolant of the values `B j`, `j ∈ S`:
`pertField S B = Σ_{j ∈ S} pertEta S j • B j`. -/
noncomputable def pertField (S : Finset ℝ) (B : ℝ → Space) (t : ℝ) : Space :=
  ∑ j ∈ S, (pertEta S j t) • B j

/-- The trigonometric perturbation of the prescribed vectors `B` over the parameter set `S`. -/
noncomputable def pertCurve (S : Finset ℝ) (B : ℝ → Space) (t : ℝ) : Space :=
  pertWeight S t • pertField S B t

end Work.Drive
