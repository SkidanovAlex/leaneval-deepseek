import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs

/-!
# The two-piece chord-endpoint curve of the low-slope reconstruction

The paper's Step 3 (the low-slope step of the odd case) reconstructs the body from the glued
Radon data through the two-power system; `GlueDefs.rhoNew R r` is the radial function of the
reconstructed body.  Its chord-endpoint curve is the two-piece curve defined here:

* for the slopes `σ ≥ 3/4` the curve is the *anchor's* (`X σ`, `Y σ`) — this is what makes the
  moment equations transfer (`momentEqs_transfer` at `a = 3/4`), since the anchor's equations
  hold on `(1 - 3τ, 1] = (0.7, 1]`;
* for `σ < 3/4` it is the radial parametrisation `σ ↦ (R (arctan σ) cos (arctan σ))` (and the
  reflected one for `x`), which is the correct chord-endpoint function for the reconstructed
  profile, because for `σ < 3/4` we have `h σ = 0` (the bump is supported in `(0.8,0.9)`) so the
  chord is *centred* and its endpoints are the radial points.

The cut is placed at `σ < 3/4` (rather than `σ ≤ 3/4`) precisely so that the agreement with the
anchor for `σ ≥ 3/4` is *definitional*, including the single endpoint `σ = 3/4`; at `σ = 3/4` the
two pieces coincide anyway (`cos (arctan (3/4)) = 4/5`, and the two-power system on the cap makes
`R (arccos (4/5)) = ρ_a (4/5)`), which is needed separately for the radial-graph identity.

The radial point of `u = cos (arctan σ)` is `ρ_new u · u`, so the profile built from this curve is
`envelopeProfile h x y`, traced by `rhoNew R r`; that identity is the `hgraph` hypothesis of
`momentEqs_lowSlopes_of_datum_ball_threshold`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The right-hand chord-endpoint function of the reconstructed body: the anchor's `Y` for
`σ ≥ 3/4`, and the radial parametrisation `R (arctan σ) cos (arctan σ)` for `σ < 3/4`. -/
def lowSlopeCurveY (R Y : ℝ → ℝ) (σ : ℝ) : ℝ :=
  if σ < 3 / 4 then R (Real.arctan σ) * Real.cos (Real.arctan σ) else Y σ

/-- The left-hand chord-endpoint function (reflected): the anchor's `X` for `σ ≥ 3/4`, and
`r (arctan σ) cos (arctan σ)` for `σ < 3/4`.  Note `r` is the radial function of the *negative*
half of the profile, so this is the positve function `-t ↦ ρ_new (-t) * (-t)` traced in the
`x`-variable. -/
def lowSlopeCurveX (r X : ℝ → ℝ) (σ : ℝ) : ℝ :=
  if σ < 3 / 4 then r (Real.arctan σ) * Real.cos (Real.arctan σ) else X σ

lemma lowSlopeCurveY_of_lt {R Y : ℝ → ℝ} {σ : ℝ} (h : σ < 3 / 4) :
    lowSlopeCurveY R Y σ = R (Real.arctan σ) * Real.cos (Real.arctan σ) := if_pos h

lemma lowSlopeCurveY_of_ge {R Y : ℝ → ℝ} {σ : ℝ} (h : 3 / 4 ≤ σ) :
    lowSlopeCurveY R Y σ = Y σ := if_neg (not_lt.mpr h)

lemma lowSlopeCurveX_of_lt {r X : ℝ → ℝ} {σ : ℝ} (h : σ < 3 / 4) :
    lowSlopeCurveX r X σ = r (Real.arctan σ) * Real.cos (Real.arctan σ) := if_pos h

lemma lowSlopeCurveX_of_ge {r X : ℝ → ℝ} {σ : ℝ} (h : 3 / 4 ≤ σ) :
    lowSlopeCurveX r X σ = X σ := if_neg (not_lt.mpr h)

/-- **Agreement with the anchor on `[3/4, ∞)`** — definitional, including the endpoint.  This is
what `momentEqs_transfer` consumes at `a = 3/4`. -/
lemma lowSlopeCurve_agree {R r X Y : ℝ → ℝ} :
    ∀ σ : ℝ, 3 / 4 ≤ σ →
      lowSlopeCurveX r X σ = X σ ∧ lowSlopeCurveY R Y σ = Y σ :=
  fun _ h => ⟨lowSlopeCurveX_of_ge h, lowSlopeCurveY_of_ge h⟩

/-- On the low-slope piece the right endpoint is literally `cos (arctan σ) * R (arctan σ)`. -/
lemma lowSlopeCurveY_eq_cos_mul {R Y : ℝ → ℝ} {σ : ℝ} (h : σ < 3 / 4) :
    lowSlopeCurveY R Y σ = Real.cos (Real.arctan σ) * R (Real.arctan σ) := by
  rw [lowSlopeCurveY_of_lt h]; ring

/-- On the low-slope piece the left endpoint is literally `cos (arctan σ) * r (arctan σ)`. -/
lemma lowSlopeCurveX_eq_cos_mul {r X : ℝ → ℝ} {σ : ℝ} (h : σ < 3 / 4) :
    lowSlopeCurveX r X σ = Real.cos (Real.arctan σ) * r (Real.arctan σ) := by
  rw [lowSlopeCurveX_of_lt h]; ring

/-- **The semicircle's chord function is the cosine of the arctangent**:
`profileX σ = cos (arctan σ)`.  This is the identity that turns every closeness statement about
the curve into an algebraic statement about `R`, `r` and `cos`/`sin` of `arctan σ` (the §4
formulas of `NOTES_CRUX_2026.md`). -/
lemma profileX_eq_cos_arctan (σ : ℝ) :
    Work.OddEnvelope.profileX σ = Real.cos (Real.arctan σ) := by
  rw [Work.OddEnvelope.profileX, Real.cos_arctan]

/-- **§4, first formula.**  On the low-slope piece the deviation of the right endpoint from
`profileX` is `cos (arctan σ) * (R (arctan σ) - 1)`. -/
lemma lowSlopeCurveY_sub_profileX {R Y : ℝ → ℝ} {σ : ℝ} (h : σ < 3 / 4) :
    lowSlopeCurveY R Y σ - Work.OddEnvelope.profileX σ =
      Real.cos (Real.arctan σ) * (R (Real.arctan σ) - 1) := by
  rw [lowSlopeCurveY_eq_cos_mul h, profileX_eq_cos_arctan]
  ring

/-- **§4, first formula, left branch.** -/
lemma lowSlopeCurveX_sub_profileX {r X : ℝ → ℝ} {σ : ℝ} (h : σ < 3 / 4) :
    lowSlopeCurveX r X σ - Work.OddEnvelope.profileX σ =
      Real.cos (Real.arctan σ) * (r (Real.arctan σ) - 1) := by
  rw [lowSlopeCurveX_eq_cos_mul h, profileX_eq_cos_arctan]
  ring

end

end Work.OddCurve.LowSlope
