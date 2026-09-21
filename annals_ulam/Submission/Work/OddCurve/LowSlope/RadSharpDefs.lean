import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogDefs

/-!
# The sharp box bounds for the low-slope odd radial pair

For the qualitative estimates of `Work.OddCurve.LowSlope.radial_system_sharp` the
linearisation of the two-power radial system is used near the ball solution `R = r = 1`.
The constants are driven by how far `R, r` and their powers stay from `1`; the hypothesis
`σ ≤ 1/8` makes the perturbation of the data small enough that the following *sharp* box
bounds hold (the crude `3/8 ≤ R^m, r^m ≤ 15/8` of `RadialLogConstruction` is far too lossy).

`SharpBox n R r` bundles the eleven facts about `R` and `r` that the estimates use.
It is symmetric under `R ↔ r` (`sharpBox_swap`), because the second-order formula for `r''`
is obtained from the one for `R''` by exchanging the two functions and negating `B`.
-/

noncomputable section

namespace Work.OddCurve.LowSlope

/-- The sharp numerical box for the radial pair: `R, r` and their `2n`-th and `(2n+2)`-th powers
lie in `[5/6, 6/5]`, the ratios `(r/R)^{2n}`, `(R/r)^{2n}` are at most `3/2`, and `R + r ≥ 5/3`. -/
def SharpBox (n : ℕ) (R r : ℝ) : Prop :=
  ((5 : ℝ) / 6 ≤ R ∧ R ≤ 6 / 5 ∧
    (5 : ℝ) / 6 ≤ R ^ (2 * n) ∧ R ^ (2 * n) ≤ 6 / 5 ∧
    (5 : ℝ) / 6 ≤ R ^ (2 * n + 2) ∧ R ^ (2 * n + 2) ≤ 6 / 5 ∧
    (5 : ℝ) / 6 ≤ r ∧ r ≤ 6 / 5 ∧
    (5 : ℝ) / 6 ≤ r ^ (2 * n) ∧ r ^ (2 * n) ≤ 6 / 5 ∧
    (5 : ℝ) / 6 ≤ r ^ (2 * n + 2) ∧ r ^ (2 * n + 2) ≤ 6 / 5 ∧
    (r / R) ^ (2 * n) ≤ 3 / 2 ∧ (R / r) ^ (2 * n) ≤ 3 / 2 ∧
    (5 : ℝ) / 3 ≤ R + r)

/-- `SharpBox` is symmetric in the two radial functions. -/
lemma sharpBox_swap {n : ℕ} {R r : ℝ} (h : SharpBox n R r) : SharpBox n r R := by
  obtain ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3⟩ := h
  exact ⟨b1, b2, b3, b4, b5, b6, a1, a2, a3, a4, a5, a6, c2, c1, by linarith⟩

end Work.OddCurve.LowSlope
