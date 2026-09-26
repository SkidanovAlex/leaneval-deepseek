import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.sweepBlurFacts

/-!
# The matching phase of the chord sweep at the wide end: vocabulary

The doubly smoothed chord sweep `Work.Drive.sweepFam r D lam δ₁ δ₂ σ` is, at a sweep parameter `σ`
close to `1`, a `C¹`-approximation of the knot after reparametrisation.  The matching used by the
fine estimate is the *piecewise affine matching phase* `Work.Drive.wideSigma` of
`Submission/Work/Drive/sweepFamWideTolDefs.lean`: at loop parameter `τ` the loop point is close to
the knot point `r (wideSigma (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam τ)`, and the rate of
the matching phase is the piecewise constant function `wideRho`.

This file fixes the **two-variable** matching phase and its **double bump average** (the two
smoothings of `sweepFam`: in the loop parameter at scale `δ₁` and in the sweep parameter at scale
`δ₂`), so that the fine estimates can be stated for plain functions of one variable.

* `Work.Drive.widePhaseFun` — the matching phase `(σ, τ) ↦ wideSigma …`;
* `Work.Drive.widePhaseBlur1` — its bump average in the loop parameter (radius `δ₁`);
* `Work.Drive.widePhaseBlur` — the further bump average in the sweep parameter (radius `δ₂`).

The doubly blurred *rate* is the pre-existing `Work.Drive.wideRateBlur` of
`sweepFamWideTolDefs.lean` (it is the same double bump average of `wideRho`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

noncomputable section

/-- **The matching phase** of the wide end, as a function of `(sweep parameter, loop parameter)`:
the piecewise affine `wideSigma` computed with the `a`-lift, the width and the gap of the sweep
parameter. -/
def widePhaseFun {d : BandArcData} (D : SweepData d) (lam : ℝ) : ℝ × ℝ → ℝ :=
  fun p => wideSigma (taR D p.1) (sweepW' D p.1) (period - sweepW' D p.1) lam p.2

/-- The bump average of the matching phase in the *loop* parameter (radius `δ₁`). -/
def widePhaseBlur1 {d : BandArcData} (D : SweepData d) (lam δ₁ σ : ℝ) (τ : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, sweepBump u * widePhaseFun D lam (σ, τ - δ₁ * u)

/-- **The doubly blurred matching phase**: the bump average of `widePhaseFun` in the loop parameter
at scale `δ₁` and in the sweep parameter at scale `δ₂` — the same two smoothings that define
`sweepFam`. -/
def widePhaseBlur {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) (τ : ℝ) : ℝ :=
  ∫ v in (-1 : ℝ)..1, sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ

@[simp] lemma widePhaseFun_apply {d : BandArcData} (D : SweepData d) (lam s t : ℝ) :
    widePhaseFun D lam (s, t) =
      wideSigma (taR D s) (sweepW' D s) (period - sweepW' D s) lam t := rfl

@[simp] lemma widePhaseBlur1_apply {d : BandArcData} (D : SweepData d) (lam δ₁ σ τ : ℝ) :
    widePhaseBlur1 D lam δ₁ σ τ =
      ∫ u in (-1 : ℝ)..1, sweepBump u *
        wideSigma (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam (τ - δ₁ * u) := rfl

@[simp] lemma widePhaseBlur_apply {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ τ : ℝ) :
    widePhaseBlur D lam δ₁ δ₂ σ τ =
      ∫ v in (-1 : ℝ)..1, sweepBump v * widePhaseBlur1 D lam δ₁ (σ - δ₂ * v) τ := rfl

end

end Work.Drive
