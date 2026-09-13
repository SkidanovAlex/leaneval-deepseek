/-
The final assembly: Theorem 1.1 of Shankar--Yuan follows from the two deep inputs of Section 5
recorded in `Submission/MasterEstimate.lean` (`AlexandrovInput` and `SavinInput`).
-/
import Submission.MasterEstimate
import Submission.MasterEstimateLimit
import Submission.InteriorGradientBoundProof
import Submission.AlexandrovAssembly
import Submission.AlexandrovAssembly2
import Submission.HessianMeasure

open HessianEstimates
open Laplacian Metric ContDiff MeasureTheory ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)
local notation "B₁(0)" => ball 0 1
local notation "‖" f "‖_C¹(" s ")" => eC1NormOn f s volume
local notation "‖" T "‖_F" => frobeniusNorm T

namespace Submission

/-- **Theorem 1.1**, conditional on the two external inputs of Proposition 3.1 (Trudinger--Wang's
gradient estimate and Chaudhuri--Trudinger's Hessian measure theorem) together with Savin's small
perturbation theorem.  All the remaining ingredients of Section 3 of the paper (in particular the
analytic core `lem:o(r²)`) are theorems of this repository. -/
theorem theorem_1_1_of_three_inputs (hG : GradientEstimateInput) (hH : WeakHessianMeasureInput)
    (hT : TaylorCoreInput) (hSavin : SavinInput) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (⊤ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0))) := by
  obtain ⟨B, hB⟩ := masterBound_exists (alexandrovInput_holds hG hH hT) hSavin
  exact theorem_1_1_of_master B hB ∞ (WithTop.coe_le_coe.mpr le_top)

/-- **Theorem 1.1**, conditional on **Savin's small perturbation theorem alone**.

This is the sharpest form of the reduction available: Trudinger's classical interior gradient
estimate is now a theorem of the repository (`Submission.interiorGradientBound_holds` in
`Submission/InteriorGradientBoundProof.lean`, derived from the interior gradient estimate for
`σ₂ = 1` by the oscillation-normalising rescaling), as are Trudinger--Wang's weighted estimate
(`Submission.classical_weighted_estimate`), the slope estimate `(point)`
(`Submission.point_estimate_limit`), Proposition 3.1 (`Submission.alexandrov_of_limit`) and the
whole of Sections 1--2 and 5. -/
theorem theorem_1_1_of_savin (hSavin : SavinInput) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (⊤ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0))) := by
  obtain ⟨B, hB⟩ := masterBound_exists_limit interiorGradientBound_holds hSavin
  exact theorem_1_1_of_master B hB ∞ (WithTop.coe_le_coe.mpr le_top)

/-- **Theorem 1.1**, conditional on Trudinger's **classical** interior gradient estimate
(`Submission.InteriorGradientBound`, quoted as Theorem 3.3 of Trudinger--Wang, *Hessian measures
II*) and Savin's small perturbation theorem `[S]` Thm 1.3.

This is the sharpest form of the reduction currently available.  The viscosity passage for the
gradient estimate is no longer an input: `Submission.classical_weighted_estimate` derives
Trudinger--Wang's weighted estimate (Cor 3.4 of *Hessian measures II*) from the classical estimate,
`Submission.point_estimate_limit` passes the resulting slope estimate to the uniform limits of
classical solutions produced by `Submission.extraction`, and
`Submission.alexandrov_of_limit` assembles Proposition 3.1 for those limits.  The Hessian measure
theorem of Chaudhuri--Trudinger and the paper's analytic core (`lem:o(r²)`) are theorems of the
repository. -/
theorem theorem_1_1_of_two_inputs_limit (hIG : InteriorGradientBound) (hSavin : SavinInput) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (⊤ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0))) := by
  obtain ⟨B, hB⟩ := masterBound_exists_limit hIG hSavin
  exact theorem_1_1_of_master B hB ∞ (WithTop.coe_le_coe.mpr le_top)

/-- **Theorem 1.1**, conditional on the two *remaining* published inputs: Trudinger--Wang's
weighted interior gradient estimate `[TW]` Cor 3.4 and Savin's small perturbation theorem `[S]`
Thm 1.3.  The Hessian-measure theorem of Chaudhuri--Trudinger is now a *theorem* of this
repository (`Submission.hessianMeasureInput_holds`, in `Submission/HessianMeasure.lean`), as is the
paper's own analytic core (Lemma `lem:o(r²)`, `Submission.taylorCoreInput_holds`). -/
theorem theorem_1_1_of_two_inputs' (hG : GradientEstimateInput) (hSavin : SavinInput) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (⊤ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0))) := by
  obtain ⟨B, hB⟩ :=
    masterBound_exists (alexandrovInput_holds' hG hessianMeasureInput_holds
      taylorCoreInput_holds) hSavin
  exact theorem_1_1_of_master B hB ∞ (WithTop.coe_le_coe.mpr le_top)

/-- **Theorem 1.1**, conditional on the three published inputs: Trudinger--Wang's weighted interior
gradient estimate `[TW]` Cor 3.4, Chaudhuri--Trudinger's Hessian measure theorem `[CT]` Thm 2.4
(in the weak form `Submission.HessianMeasureInput`, which only asks for the Hessian measure -- the
weak gradient is derived from `[TW]` in `Submission.GradFromGradient`), and Savin's small
perturbation theorem `[S]` Thm 1.3.  The paper's own analytic core (Lemma `lem:o(r²)`) is the
theorem `Submission.taylorCoreInput_holds`. -/
theorem theorem_1_1_of_three_inputs' (hG : GradientEstimateInput) (hHM : HessianMeasureInput)
    (hSavin : SavinInput) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (⊤ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0))) := by
  obtain ⟨B, hB⟩ := masterBound_exists (alexandrovInput_holds' hG hHM taylorCoreInput_holds) hSavin
  exact theorem_1_1_of_master B hB ∞ (WithTop.coe_le_coe.mpr le_top)

/-- **Theorem 1.1**, conditional on the two external inputs (Trudinger--Wang and
Chaudhuri--Trudinger) and Savin's theorem; the analytic core is `taylorCoreInput_holds`. -/
theorem theorem_1_1_of_two_inputs (hG : GradientEstimateInput) (hH : WeakHessianMeasureInput)
    (hSavin : SavinInput) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (⊤ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0))) := by
  obtain ⟨B, hB⟩ := masterBound_exists (alexandrovInput_holds hG hH taylorCoreInput_holds) hSavin
  exact theorem_1_1_of_master B hB ∞ (WithTop.coe_le_coe.mpr le_top)

/-- **Theorem 1.1**, conditional on the Alexandrov and Savin inputs. -/
theorem theorem_1_1_of_inputs (hAlex : AlexandrovInput) (hSavin : SavinInput) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (⊤ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0))) := by
  obtain ⟨B, hB⟩ := masterBound_exists hAlex hSavin
  exact theorem_1_1_of_master B hB ∞ (WithTop.coe_le_coe.mpr le_top)

end Submission
