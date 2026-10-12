import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import ChallengeDeps
import Submission.KernelIds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — packaged witness: `(χ⋆χ) ≥ 1/2` on `ball 0 chiR0`

`CubicChi.half_lower_ball_of_continuousAt_one` (applied to the continuous
`χ⋆χ` with value `1` at `0`) gives an existential `r₀`; this module packages
the choice into a global constant so that later modules (kernel identities,
locPotential, regime instantiation) can reference `chiR0` directly instead of
re-extracting witnesses.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real Convolution

namespace Submission.BoseGases

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A global radius where `(χ⋆χ) ≥ 1/2` (chosen from the continuity of
`χ⋆χ` at `0`, value `1`). -/
noncomputable def chiR0 : ℝ :=
  Classical.choose (half_lower_ball_of_continuousAt_one
    (conv_contDiff.continuous.continuousAt) (conv3_at_zero))

/-- `0 < chiR0`. -/
theorem chiR0_pos : 0 < chiR0 := by
  have h := Classical.choose_spec (half_lower_ball_of_continuousAt_one
    (conv_contDiff.continuous.continuousAt) (conv3_at_zero))
  exact h.1

/-- `(χ⋆χ)(x) ≥ 1/2` for `‖x‖ ≤ chiR0`. -/
theorem chiR0_half (x : ℝ³) (hx : ‖x‖ ≤ chiR0) : 1 / 2 ≤ conv3 chi chi x := by
  have h := Classical.choose_spec (half_lower_ball_of_continuousAt_one
    (conv_contDiff.continuous.continuousAt) (conv3_at_zero))
  exact h.2 x (by simpa [chiR0] using hx)

/-- The scaled-convolution lower bound on the `R`-ball: when `R ≤ ℓ·chiR0`,
`convScale ℓ (x−y) ≥ 1/2` for `‖x−y‖ ≤ R`. -/
theorem convScale_ge_half_ball {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {z : ℝ³} (hz : ‖z‖ ≤ R) :
    1 / 2 ≤ convScale ℓ z := by
  have hz' : ‖(ℓ⁻¹) • z‖ ≤ chiR0 := by
    rw [norm_smul]
    have hℓi : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr (le_of_lt hℓ)
    calc
      |ℓ⁻¹| * ‖z‖ ≤ ℓ⁻¹ * R := by
        rw [abs_of_nonneg hℓi]
        exact mul_le_mul_of_nonneg_left hz hℓi
      _ ≤ chiR0 := by
        calc ℓ⁻¹ * R ≤ ℓ⁻¹ * (ℓ * chiR0) := mul_le_mul_of_nonneg_left hRℓ hℓi
        _ = chiR0 := by field_simp [ne_of_gt hℓ]
  have hhalf := chiR0_half ((ℓ⁻¹) • z) hz'
  simpa [convScale] using hhalf

end BoseGases

end Submission
