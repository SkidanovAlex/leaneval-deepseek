import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepBlurFacts
import Submission.Work.Drive.sweepLoopProfileDefs

/-!
# The matched parametrisation of the chord sweep at the wide end

Vocabulary for the wide-end estimate with tolerance
(`Submission/Work/Drive/sweepFam_wideEnd_estimate_tol`).

The doubly smoothed chord sweep `Work.Drive.sweepFam r D lam δ₁ δ₂ σ` at a sweep parameter `σ`
close to `1` is, after a reparametrisation of the loop parameter, `C¹`-close to the knot `r`.
The reparametrisation used by the estimate is the inverse of the *blurred matching phase*
`widePsiBar`: the bump-average of the explicit, piecewise affine matching phase `wideSigma`,
whose rate is the piecewise constant `wideRho`.

For loop fraction `u = sweepParam τ ∈ [0,1]` the loop follows

* the **arc** of the knot (from fraction `lam` to fraction `1 - lam` of the retained arc) for
  `u ≤ 1/2`,
* the **first chamfer** (a straight segment) for `u ∈ (1/2, 1/2 + lam/2]`,
* the **chord** of the omitted piece for `u ∈ (1/2 + lam/2, 1 - lam/2]`,
* the **second chamfer** for `u ∈ (1 - lam/2, 1]`,

and the knot parameter matched to `u` is the piecewise-affine function `wideSfrac`
(`ta` is `taR D σ`, `w = sweepW' D σ`, `d = period - w`).

## Contents

* `Work.Drive.wideSfrac`, `Work.Drive.wideSigma` — the matched knot parameter;
* `Work.Drive.wideRho` — the rate `dΣ/dτ`;
* `Work.Drive.wideRhoBar`, `Work.Drive.widePsiBar` — the blurred rate and phase;
* basic zone evaluations and period-shift properties.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-! ## The matched parameter and the rate -/

/-- **The knot parameter matched to the loop fraction `u`.**  With `ta` the `a`-lift of the sweep
parameter, `w = tb - ta` the width of the retained arc, `d = period - w` the length of the omitted
piece and `lam` the chamfer fraction, the loop at fraction `u` matches the knot parameter

* `ta + (lam + (1 - 2 lam) * 2 u) * w` for `u ≤ 1/2` (the arc zone),
* `ta + (1 - lam) * w + (2 u - 1) * period` for `1/2 ≤ u ≤ 1/2 + lam/2` (first chamfer),
* `ta + w + lam * d + (1 - 2 lam) * d * (u - 1/2 - lam/2)/(1/2 - lam)` for
  `1/2 + lam/2 ≤ u ≤ 1 - lam/2` (the chord of the omitted piece),
* `ta + w + (1 - lam) * d + (2 u - 2 + lam) * period` for `1 - lam/2 ≤ u` (second chamfer). -/
def wideSfrac (ta w d lam u : ℝ) : ℝ :=
  if u ≤ 1 / 2 then ta + (lam + (1 - 2 * lam) * (2 * u)) * w
  else if u ≤ 1 / 2 + lam / 2 then ta + (1 - lam) * w + (2 * u - 1) * period
  else if u ≤ 1 - lam / 2 then
    ta + w + lam * d + ((1 - 2 * lam) * d) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam))
  else ta + w + (1 - lam) * d + (2 * u - 2 + lam) * period

/-- **The matching phase**: loop parameter `τ ↦` matched knot parameter.  Written as `τ` plus a
periodic deviation, so that it is manifestly period-shifting. -/
def wideSigma (ta w d lam τ : ℝ) : ℝ :=
  τ + (wideSfrac ta w d lam (sweepParam τ) - sweepParam τ * period)

/-- **The rate `dΣ/dτ`**: `2 (1 - 2 lam) w / period` on the arc zone, `2` on the two chamfers and
`(1 - 2 lam) d / (period (1/2 - lam))` on the chord zone. -/
def wideRho (w d lam u : ℝ) : ℝ :=
  if u ≤ 1 / 2 then (1 - 2 * lam) * (2 * w / period)
  else if u ≤ 1 / 2 + lam / 2 then 2
  else if u ≤ 1 - lam / 2 then (1 - 2 * lam) * d / (period * (1 / 2 - lam))
  else 2

/-- **The blurred rate**: the bump-average of `wideRho` in the loop parameter. -/
def wideRhoBar (w d lam δ₁ τ : ℝ) : ℝ :=
  ∫ v in (-1 : ℝ)..1, sweepBump v * wideRho w d lam (sweepParam (τ - δ₁ * v))

/-- **The blurred (smoothed) phase**: the bump-average of the matching phase `wideSigma`. -/
def widePsiBar (ta w d lam δ₁ τ : ℝ) : ℝ :=
  ∫ v in (-1 : ℝ)..1, sweepBump v * wideSigma ta w d lam (τ - δ₁ * v)

/-! ## Period shifts -/

/-- **The matching phase is period-shifting.** -/
lemma wideSigma_add_period (ta w d lam τ : ℝ) :
    wideSigma ta w d lam (τ + period) = wideSigma ta w d lam τ + period := by
  have : sweepParam (τ + period) = sweepParam τ := sweepParam_add_period τ
  simp only [wideSigma, this]
  ring

/-! ## Zone evaluations -/

lemma wideSfrac_arc {ta w d lam u : ℝ} (h : u ≤ 1 / 2) :
    wideSfrac ta w d lam u = ta + (lam + (1 - 2 * lam) * (2 * u)) * w := by
  simp only [wideSfrac, if_pos h]

lemma wideSfrac_chamfer₁ {ta w d lam u : ℝ} (h1 : ¬ u ≤ 1 / 2)
    (h2 : u ≤ 1 / 2 + lam / 2) :
    wideSfrac ta w d lam u = ta + (1 - lam) * w + (2 * u - 1) * period := by
  simp only [wideSfrac, if_neg h1, if_pos h2]

lemma wideSfrac_chord {ta w d lam u : ℝ} (h1 : ¬ u ≤ 1 / 2) (h2 : ¬ u ≤ 1 / 2 + lam / 2)
    (h3 : u ≤ 1 - lam / 2) :
    wideSfrac ta w d lam u
      = ta + w + lam * d + ((1 - 2 * lam) * d) * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) := by
  simp only [wideSfrac, if_neg h1, if_neg h2, if_pos h3]

lemma wideSfrac_chamfer₂ {ta w d lam u : ℝ} (h1 : ¬ u ≤ 1 / 2) (h2 : ¬ u ≤ 1 / 2 + lam / 2)
    (h3 : ¬ u ≤ 1 - lam / 2) :
    wideSfrac ta w d lam u = ta + w + (1 - lam) * d + (2 * u - 2 + lam) * period := by
  simp only [wideSfrac, if_neg h1, if_neg h2, if_neg h3]

lemma wideRho_arc {w d lam u : ℝ} (h : u ≤ 1 / 2) :
    wideRho w d lam u = (1 - 2 * lam) * (2 * w / period) := by
  simp only [wideRho, if_pos h]

lemma wideRho_chamfer₁ {w d lam u : ℝ} (h1 : ¬ u ≤ 1 / 2) (h2 : u ≤ 1 / 2 + lam / 2) :
    wideRho w d lam u = 2 := by
  simp only [wideRho, if_neg h1, if_pos h2]

lemma wideRho_chord {w d lam u : ℝ} (h1 : ¬ u ≤ 1 / 2) (h2 : ¬ u ≤ 1 / 2 + lam / 2)
    (h3 : u ≤ 1 - lam / 2) :
    wideRho w d lam u = (1 - 2 * lam) * d / (period * (1 / 2 - lam)) := by
  simp only [wideRho, if_neg h1, if_neg h2, if_pos h3]

lemma wideRho_chamfer₂ {w d lam u : ℝ} (h1 : ¬ u ≤ 1 / 2) (h2 : ¬ u ≤ 1 / 2 + lam / 2)
    (h3 : ¬ u ≤ 1 - lam / 2) :
    wideRho w d lam u = 2 := by
  simp only [wideRho, if_neg h1, if_neg h2, if_neg h3]

/-- The junction values of the matching phase (in the fraction variable): the four pieces agree at
the three junctions, and the value at `u = 1` is the value at `u = 0` plus one period. -/
lemma wideSfrac_half {ta w lam : ℝ} :
    wideSfrac ta w (period - w) lam (1 / 2) = ta + (1 - lam) * w := by
  rw [wideSfrac_arc le_rfl]; ring

lemma wideSfrac_u2 {ta w lam : ℝ} (h0 : 0 < lam) :
    wideSfrac ta w (period - w) lam (1 / 2 + lam / 2) = ta + w + lam * (period - w) := by
  have hlt : ¬ (1 / 2 + lam / 2 : ℝ) ≤ 1 / 2 := by linarith
  rw [wideSfrac_chamfer₁ hlt le_rfl]
  ring

lemma wideSfrac_u3 {ta w lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) :
    wideSfrac ta w (period - w) lam (1 - lam / 2) = ta + w + (1 - lam) * (period - w) := by
  have h1' : ¬ (1 - lam / 2 : ℝ) ≤ 1 / 2 := by linarith
  have h2' : ¬ (1 - lam / 2 : ℝ) ≤ 1 / 2 + lam / 2 := by linarith
  rw [wideSfrac_chord h1' h2' le_rfl,
    show (1 - lam / 2 - (1 / 2 + lam / 2) : ℝ) = 1 / 2 - lam by ring,
    div_self (ne_of_gt (by linarith : (0 : ℝ) < 1 / 2 - lam))]
  ring

lemma wideSfrac_one {ta w lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    wideSfrac ta w (period - w) lam 1 = ta + lam * w + period := by
  have h1' : ¬ (1 : ℝ) ≤ 1 / 2 := by norm_num
  have h2' : ¬ (1 : ℝ) ≤ 1 / 2 + lam / 2 := by linarith
  have h3' : ¬ (1 : ℝ) ≤ 1 - lam / 2 := by linarith
  rw [wideSfrac_chamfer₂ h1' h2' h3']
  ring

lemma wideSfrac_zero {ta w lam : ℝ} : wideSfrac ta w (period - w) lam 0 = ta + lam * w := by
  rw [wideSfrac_arc (by norm_num : (0:ℝ) ≤ 1/2)]; ring

/-- **Junction continuity in the fraction variable**: the value at `1` is the value at `0`
plus the total `s`-length `period`. -/
lemma wideSfrac_periodicity {ta w lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    wideSfrac ta w (period - w) lam 1 = wideSfrac ta w (period - w) lam 0 + period := by
  rw [wideSfrac_one h0 h1, wideSfrac_zero]

/-! ## The matching phase of the wide end and its blurred rate -/

/-- **The matched phase of the wide end**, as a function of the loop parameter: the piecewise affine
`wideSigma` computed with the `a`-lift, the width and the gap of the sweep parameter `σ`. -/
def wideSig {d : BandArcData} (D : SweepData d) (lam σ : ℝ) : ℝ → ℝ :=
  wideSigma (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam

/-- **The doubly blurred rate of the matched phase**: the bump average of `wideRho` in the loop
parameter (radius `δ₁`) and in the sweep parameter (radius `δ₂`).  It is the rate of the phase
`wideTheta`, and it matches the double smoothing used in the definition of `sweepFam`. -/
def wideRateBlur {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ τ : ℝ) : ℝ :=
  ∫ v in (-1 : ℝ)..1, sweepBump v * (∫ u in (-1 : ℝ)..1, sweepBump u *
      wideRho (sweepW' D (σ - δ₂ * v)) (period - sweepW' D (σ - δ₂ * v)) lam
        (sweepParam (τ - δ₁ * u)))

/-- **The matching phase at the wide end**: the primitive of the doubly blurred rate, anchored at
the matched knot parameter of the loop's start point.  It is `C^∞` and `period`-shifting by
construction, with derivative `wideRateBlur`. -/
def wideTheta {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) (τ : ℝ) : ℝ :=
  taR D σ + lam * sweepW' D σ + ∫ s in (0 : ℝ)..τ, wideRateBlur D lam δ₁ δ₂ σ s

@[simp] lemma wideSig_apply {d : BandArcData} (D : SweepData d) (lam σ τ : ℝ) :
    wideSig D lam σ τ = wideSigma (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam τ := rfl

@[simp] lemma wideTheta_zero {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ σ : ℝ) :
    wideTheta D lam δ₁ δ₂ σ 0 = taR D σ + lam * sweepW' D σ := by
  simp [wideTheta]

/-- The matched phase is `period`-shifting. -/
lemma wideSig_add_period {d : BandArcData} (D : SweepData d) (lam σ τ : ℝ) :
    wideSig D lam σ (τ + period) = wideSig D lam σ τ + period :=
  wideSigma_add_period _ _ _ _ _

end Work.Drive
