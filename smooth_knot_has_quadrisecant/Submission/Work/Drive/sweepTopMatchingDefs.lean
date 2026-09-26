import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepWideEndDefs
import Submission.Work.Drive.sweepFamWideTolDefs

/-!
# The matched parametrisation of the top end of the chord sweep (vocabulary)

At the top of the sweep window (`σ = 1 - ε'` with `ε' > 0` small) the doubly smoothed chamfered
loop
`h := Work.Drive.sweepFam r D lam δ₁ δ₂ σ`
is a reparametrised copy of the knot.  Concretely the *matching phase* is the piecewise affine
function `wideSfrac` (in the profile variable) of `Work.Drive.sweepFamWideTolDefs`, with
`ta = taR D σ`, `w = sweepW' D σ` and `d = period - w`; its (a.e.) rate is the piecewise constant
`wideRho`.

This file fixes the *smoothed* rate and phase that are used by the estimate:

* `topRateProf`   — the piecewise constant rate profile `wideRho w d lam`;
* `topRateBlur1`  — its bump average in the loop parameter (radius `δ₁`);
* `topRateB`      — its further bump average in the sweep parameter (radius `δ₂`) — matching the
  two smoothings of `sweepFam`;
* `topThetaB`     — the matching phase `Θ`, defined as the primitive of `topRateB` anchored at the
  value `taR D σ + lam * sweepW' D σ = wideSfrac ta w d lam 0`, so that it is `C^∞` by
  construction and `deriv Θ = rate`.

Everything is `period`-periodic (resp. `period`-shifting) exactly as `sweepFam` (resp. the
matching phase) is.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-- The piecewise constant rate of the matching parameter at sweep parameter `σ`. -/
def topRateProf {d : BandArcData} (D : SweepData d) (lam σ : ℝ) : ℝ → ℝ :=
  fun u => wideRho (sweepW' D σ) (period - sweepW' D σ) lam u

/-- The bump average of the rate profile in the loop parameter (radius `δ₁`). -/
def topRateBlur1 {d : BandArcData} (D : SweepData d) (lam δ₁ σ : ℝ) (τ : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, sweepBump u * topRateProf D lam σ (sweepParam (τ - δ₁ * u))

/-- The doubly blurred rate: also averaged in the sweep parameter (radius `δ₂`), matching the two
smoothings in the definition of `sweepFam`. -/
def topRateB {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) (τ : ℝ) : ℝ :=
  ∫ v in (-1 : ℝ)..1, sweepBump v * topRateBlur1 D lam δ₁ (σ - δ₂ * v) τ

/-- The matching phase of the top end: the primitive of the doubly blurred rate, anchored at the
matched parameter of the loop's start point. -/
def topThetaB {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) (τ : ℝ) : ℝ :=
  taR D σ + lam * sweepW' D σ + ∫ s in (0 : ℝ)..τ, topRateB D lam δ₁ δ₂ σ s

/-- The (raw, matched) knot parameter of the loop at sweep parameter `σ`. -/
def topSigma {d : BandArcData} (D : SweepData d) (lam σ : ℝ) : ℝ → ℝ :=
  wideSigma (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam

@[simp] lemma topSigma_apply {d : BandArcData} (D : SweepData d) (lam σ τ : ℝ) :
    topSigma D lam σ τ =
      wideSigma (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam τ := rfl

@[simp] lemma topRateProf_apply {d : BandArcData} (D : SweepData d) (lam σ u : ℝ) :
    topRateProf D lam σ u = wideRho (sweepW' D σ) (period - sweepW' D σ) lam u := rfl

@[simp] lemma topRateBlur1_apply {d : BandArcData} (D : SweepData d) (lam δ₁ σ τ : ℝ) :
    topRateBlur1 D lam δ₁ σ τ =
      ∫ u in (-1 : ℝ)..1, sweepBump u * wideRho (sweepW' D σ) (period - sweepW' D σ) lam
        (sweepParam (τ - δ₁ * u)) := rfl

@[simp] lemma topThetaB_apply {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ τ : ℝ) :
    topThetaB D lam δ₁ δ₂ σ τ =
      taR D σ + lam * sweepW' D σ + ∫ s in (0 : ℝ)..τ, topRateB D lam δ₁ δ₂ σ s := rfl

@[simp] lemma topThetaB_zero {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) :
    topThetaB D lam δ₁ δ₂ σ 0 = taR D σ + lam * sweepW' D σ := by
  simp [topThetaB]

/-- `topSigma` is `period`-shifting. -/
lemma topSigma_add_period {d : BandArcData} (D : SweepData d) (lam σ τ : ℝ) :
    topSigma D lam σ (τ + period) = topSigma D lam σ τ + period :=
  wideSigma_add_period _ _ _ _ _

/-- `topSigma (τ)` is `wideSfrac` of the profile, plus one period per wrap. -/
lemma topSigma_eq_wideSfrac {d : BandArcData} (D : SweepData d) (lam σ τ : ℝ) :
    topSigma D lam σ τ =
      wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam τ)
        + (⌊τ / period⌋ : ℤ) * period := by
  have h1 : (τ / period) * period = τ := div_mul_cancel₀ τ period_ne_zero
  have hk : sweepParam τ * period = τ - (⌊τ / period⌋ : ℤ) * period := by
    simp only [sweepParam, sub_mul, h1]
  simp only [topSigma, topSigma_apply, wideSigma]
  linarith

/-- The knot point of the matching phase is the `wideSfrac` point of the profile. -/
lemma r_topSigma_eq_wideSfrac {r : ℝ → Space} (hr : Function.Periodic r period)
    {d : BandArcData} (D : SweepData d) (lam σ τ : ℝ) :
    r (topSigma D lam σ τ) =
      r (wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam τ)) := by
  rw [topSigma_eq_wideSfrac]
  exact (hr.int_mul (⌊τ / period⌋))
    (wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam τ))

end Work.Drive
