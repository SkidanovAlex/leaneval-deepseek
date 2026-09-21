import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddCurve.LowSlope.GlueIdent
import Submission.Work.OddCurve.LowSlope.AnchorRadialClose
import Submission.Work.OddCurve.LowSlope.step3_anchor_data

/-!
# The two-power data of the low-slope reconstruction, with the endpoint at `α = π/2`

The low-slope step reconstructs the radial functions `R, r` of the new body from the *glued*
Radon data (`GlueF`, `GlueG`) through the two-power system

`R^{2n+2} + r^{2n+2} = Φ_h(α)/cos²α = 2 + GlueA α`,  `R^{2n+1} - r^{2n+1} = Ψ_h(α)/cos α = GlueB α`.

The naive definitions `GlueA = GluePhi/cos² - 2`, `GlueB = GluePsi/cos` are unusable *at*
`α = π/2`: since `Real.cos (π/2) = 0` and Lean's division is total, the value there is `0/0 - 2
= -2`, whereas the endpoint condition of the two-power system (`R (π/2) = r (π/2) = 1`) needs
`A (π/2) = B (π/2) = 0` (equivalently: the data at `c = 0` is the ball's, hence the radial
function is `1` at the pole).

The fix is by *analytic continuation*: for `cos α < 4/5` the glued datum is the anchor's
(`gluedPhi_of_lt`), so `GlueA α = ρ_a(cos α)^{2n+2} + ρ_a(-cos α)^{2n+2} - 2` there
(`GlueA_eq_cap`), and for `α → π/2` this expression tends to `0` because `ρ_a 0 = 1`.  Hence we
*define* the data by that expression for `cos α < 4/5` (which is a neighbourhood of `π/2` in the
`α` variable) and by `GlueA`/`GlueB` for `cos α ≥ 4/5`; the two pieces agree on a neighbourhood
of `cos α = 4/5` (both are `ρ_a(±cos α)`-combinations there, by the junction), so the resulting
function is `C^∞` on `(0, π/2) ∪ {π/2}` and satisfies the endpoint conditions.

Both functions are *even* in `α ↦ π/2 - α` in the sense that they are functions of `cos α`;
hence their derivatives at `α = 0` vanish.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The first datum of the two-power system, continued at `α = π/2`.

For `cos α < 4/5` (a neighbourhood of `π/2`) it is the anchor's radial-function combination
(which is `0` at `π/2`), and for `cos α ≥ 4/5` it is the glued datum's deviation.  On
`cos α < 4/5` the two expressions coincide, so this is the analytic continuation of
`GlueA`.  -/
def glueA (n : ℕ) (ρ : ℝ → ℝ) (α : ℝ) : ℝ :=
  if Real.cos α < 4 / 5 then ρ (Real.cos α) ^ (2 * n + 2) + ρ (-(Real.cos α)) ^ (2 * n + 2) - 2
  else GlueA n ρ α

/-- The second datum of the two-power system, continued at `α = π/2`. -/
def glueB (n : ℕ) (ρ : ℝ → ℝ) (α : ℝ) : ℝ :=
  if Real.cos α < 4 / 5 then ρ (Real.cos α) ^ (2 * n + 1) - ρ (-(Real.cos α)) ^ (2 * n + 1)
  else GlueB n ρ α

lemma glueA_of_lt {n : ℕ} {ρ : ℝ → ℝ} {α : ℝ} (hα : Real.cos α < 4 / 5) :
    glueA n ρ α = ρ (Real.cos α) ^ (2 * n + 2) + ρ (-(Real.cos α)) ^ (2 * n + 2) - 2 := if_pos hα

lemma glueA_of_ge {n : ℕ} {ρ : ℝ → ℝ} {α : ℝ} (hα : 4 / 5 ≤ Real.cos α) :
    glueA n ρ α = GlueA n ρ α := if_neg (not_lt.mpr hα)

lemma glueB_of_lt {n : ℕ} {ρ : ℝ → ℝ} {α : ℝ} (hα : Real.cos α < 4 / 5) :
    glueB n ρ α = ρ (Real.cos α) ^ (2 * n + 1) - ρ (-(Real.cos α)) ^ (2 * n + 1) := if_pos hα

lemma glueB_of_ge {n : ℕ} {ρ : ℝ → ℝ} {α : ℝ} (hα : 4 / 5 ≤ Real.cos α) :
    glueB n ρ α = GlueB n ρ α := if_neg (not_lt.mpr hα)

/-- At `α = π/2` the first datum is `0` as soon as the radial function is `1` at the pole. -/
lemma glueA_at_pi_div_two {n : ℕ} {ρ : ℝ → ℝ} (hρ0 : ρ 0 = 1) :
    glueA n ρ (Real.pi / 2) = 0 := by
  rw [glueA_of_lt (by rw [Real.cos_pi_div_two]; norm_num)]
  rw [Real.cos_pi_div_two, neg_zero, hρ0]
  norm_num

/-- At `α = π/2` the second datum is `0`. -/
lemma glueB_at_pi_div_two (n : ℕ) (ρ : ℝ → ℝ) : glueB n ρ (Real.pi / 2) = 0 := by
  rw [glueB_of_lt (by rw [Real.cos_pi_div_two]; norm_num)]
  rw [Real.cos_pi_div_two, neg_zero]
  ring

end

end Work.OddCurve.LowSlope
