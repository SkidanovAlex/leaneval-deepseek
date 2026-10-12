import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.MeanValue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Newtonian identity `∫ (Δφ)(x)/‖x−y‖ dx = −4π·φ(y)` (Layer 3)

The heavy analysis lives in `Submission.NewtonIdAux` (Green identities, vanishing lemmas,
radial cutoffs, translations) and the origin mean-value identity is
`Submission.MeanValue.newton_integral_delta_zero`.  This file only assembles the final
statement by translating the origin identity to an arbitrary centre `y`
(`newton_integral_delta_of_zero`).
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Newton identity: `∫ (Δφ)(x)/‖x−y‖ dx = −4π·φ(y)` for smooth compactly supported `φ`. -/
theorem newton_integral_delta {y : ℝ³} (φ : ℝ³ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφcs : HasCompactSupport φ) :
    (∫ x : ℝ³, (Δ φ) x * (‖x - y‖ : ℝ)⁻¹) = -4 * π * φ y := by
  exact newton_integral_delta_of_zero φ hφ hφcs
    (fun ψ hψ hcs => newton_integral_delta_zero ψ hψ hcs)

end Submission.BoseGases
