/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeStepOneAux.Defs` — the auxiliary `Prop`s used by the proof of `H2W.AeStepOneSig`

This file fixes the single auxiliary `Prop` that the two halves of the level-`0` estimate
`Work.FTS.EllipticEst.H2W.AeStepOneSig` share:

* `SigmaCoercive` — the `σ`-coercivity of the angular operator
  `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` on a slice of class `C²` on the *open* interval
  `(0,π/2)`, with the two linear vanishing bounds `|u θ| ≤ C·θ`, `|u θ| ≤ C·(π/2-θ)` and the
  derivative bound `|deriv u θ| ≤ C`, and the four `σ`-integrability hypotheses:

  `((1-η)/(1+η)) ∫_θ (u')² σ ≤ ∫_θ (Lzero1 u) u σ + K ∫_θ u² σ`,  `σ = sin(2θ)^{-η}`,

  with `K` universal.  This is exactly `Work.FTS.EllipticEst.Honest.HonSliceSigmaLower` with the
  hypothesis `ContDiffOn ℝ 1 u (Icc 0 (π/2))` replaced by the three explicit bounds, which is the
  form in which the *almost everywhere* class `Work.FTS.EllipticEst.H2W.Ae.AeData` can supply it
  (the slices are only `C^∞` on the open quadrant, and the endpoint vanishing holds only a.e.).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeStepOneAux

set_option autoImplicit false

/-- **The sharp Hardy inequality on `Iθ` with the *same* weight on both sides, for slices given
only by explicit endpoint bounds** (no `C¹`-on-the-closed-interval hypothesis): there is `C` with
`∫_θ f²/sin(2θ)^{2+η} ≤ (1+η)⁻² ∫_θ (f')²/sin(2θ)^η + C ∫_θ f²/sin(2θ)^η`
for every `f` of class `C¹` on the open interval with `|f θ| ≤ C₀ min(θ, π/2-θ)` and
`|deriv f θ| ≤ C₀`.  The constant `(1+η)⁻²` is sharp and is what makes the `σ`-coercivity of
`Lzero1` work. -/
def HardyBddEta : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (C₀ : ℝ), 0 ≤ C₀ →
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ C₀ * θ) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ C₀ * (Real.pi / 2 - θ)) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ C₀) →
    (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
      ≤ 1 / (1 + Work.Spaces.eta) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (deriv f θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
        + C * (∫ θ in Work.Spaces.Iθ,
              (f θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta))

/-- **The `σ`-coercivity of `Lzero1` on a slice, with explicit endpoint bounds.** -/
def SigmaCoercive : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (u : ℝ → ℝ) (C : ℝ), 0 ≤ C →
    ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ C * θ) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ C * (Real.pi / 2 - θ)) →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u θ| ≤ C) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
    ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
        * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.Lzero1 u θ * u θ * Work.FTS.EllipticEst.sEta θ)
        + K * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)

end Work.FTS.EllipticEst.AeStepOneAux
