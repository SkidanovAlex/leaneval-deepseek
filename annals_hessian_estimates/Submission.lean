import ChallengeDeps
import Submission.Helpers
import Submission.FinalAssembly
import Submission.SavinTheorem

open HessianEstimates
open Laplacian Metric ContDiff MeasureTheory ENNReal

set_option autoImplicit false
local notation "‖" f "‖_C¹(" s ")" => eC1NormOn f s volume
local notation "‖" T "‖_F" => frobeniusNorm T
local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)
local notation "B₁(0)" => ball 0 1

namespace Submission

/-  The proof of `theorem_1_1` is complete modulo exactly **two** deep published theorems, both of
which are recorded as hypotheses (never as axioms) in `Submission/MasterEstimate.lean`:

  * `Submission.GradientEstimateInput` -- Trudinger--Wang's weighted interior gradient estimate
    ([TW] Cor 3.4) for viscosity solutions of `σ₂ = 1` with `Δu > 0`;
  * `Submission.SavinInput`             -- Savin's small perturbation theorem [S, Thm 1.3] in the
    form used in Step 2 of the paper's Section 5.

Everything else is proved, in particular

  * `Submission.hessianMeasureInput_holds` -- the Chaudhuri--Trudinger Hessian measure theorem
    `[CT]` Thm 2.4 (`Submission/HessianMeasure.lean`),
  * `Submission.taylorCoreInput_holds`     -- the paper's own analytic core, Lemma `lem:o(r²)`
    (`Submission/TaylorCore.lean`),

so that

  `Submission.theorem_1_1_of_savin (hSavin : SavinInput) : <the statement below>`

i.e. the challenge theorem is now reduced to **Savin's small perturbation theorem alone**.
Trudinger's classical interior gradient estimate `Submission.InteriorGradientBound` is a theorem of
the repository (`Submission.interiorGradientBound_holds`,
`Submission/InteriorGradientBoundProof.lean`), obtained from the interior gradient estimate for
`σ₂ = 1` (`Submission.interior_gradient_bound`) by the oscillation-normalising rescaling
`x ↦ y + √(M-m) x`, `u ↦ (u - m)/(M-m)`; from it, Trudinger--Wang's weighted estimate
(Corollary 3.4 of *Hessian measures II*), the slope estimate `(point)`, Proposition 3.1 and the
whole of Sections 1--5 follow.  The earlier, weaker reduction is also kept:

where

  * `Submission.InteriorGradientBound` -- Trudinger's *classical* interior gradient estimate for
    solutions of `σ₂ = 1` with `Δu > 0` (Theorem 3.3 of Trudinger--Wang, *Hessian measures II*;
    `Submission/WeightedGradientReduction.lean`).  This is the sharpest available form of the
    first input: `Submission.classical_weighted_estimate` derives Trudinger--Wang's weighted
    estimate (Corollary 3.4 of the same paper) from it via the interpolation inequality of
    `Commons.Measure.WeightedInterpolation.weighted_le_interpolation` and
    `Commons.Measure.WeightedInterpolation.weighted_lipschitz_of_osc`;
    `Submission.point_estimate_limit` (`Submission/AlexandrovLimit.lean`) passes the resulting
    slope estimate `(point)` to the uniform limits of classical solutions produced by
    `Submission.extraction`, and `Submission.alexandrov_of_limit`
    (`Submission/MasterEstimateLimit.lean`) assembles Proposition 3.1 for those limits.  The old
    route with the viscosity statement `Submission.GradientEstimateInput` is retained as

  `Submission.theorem_1_1_of_two_inputs' (hG : GradientEstimateInput) (hSavin : SavinInput)`


(`Submission/FinalAssembly.lean`), obtained by composing

  * `Submission.theorem_1_1_of_master` (`Submission/MasterReduction.lean`) -- the normalisation
    `u ↦ 16 u (·/4)` and the passage from the essential-sup `C¹` norm to the `L^∞` bounds,
  * `Submission.alexandrovInput_holds'` (`Submission/AlexandrovAssembly2.lean`) -- Proposition 3.1
    of the paper from the two inputs above, and
  * `Submission.masterBound_exists` (`Submission/MasterEstimate.lean`) -- the whole of Section 5:
    the contradiction argument, Arzelà--Ascoli, stability of viscosity solutions
    (`Submission/Viscosity.lean`), the `G` reformulation (`Submission/GOperator.lean`), the inputs,
    and Corollary 2.5 (`Submission/DoublingMovingCenter.lean`).

See `Submission/Roadmap.md`, sections "SESSION 6" and "SESSION 16", for the details.  -/

theorem theorem_1_1 : ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (∞ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0))) := by
  exact theorem_1_1_of_savin savinInput_holds

end Submission
