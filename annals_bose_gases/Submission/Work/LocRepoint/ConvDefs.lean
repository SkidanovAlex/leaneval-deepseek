import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.KernelIds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.LocRepoint.ConvDefs` — an explicit lower bound for `convScale` on a ball

`convScale ℓ z = (χ⋆χ)(z/ℓ)` is the `ℓ`-scale convolution factor of the corpus global kernel
`wPairC ℓ`.  The packaged regime used throughout the repointed localisation layer is the
`chiR0` one (`R ≤ ℓ·chiR0`, `Submission.ChiWitness.chiR0_half`); the constant below is the
*explicit* alternative used where `chiR0` is not available but `R < ℓ/2` is, i.e. where the
potential's range is smaller than half the box.

`χ = chiBase/√chiNormSq` with `chiBase = chiBump : ContDiffBump (0 : ℝ³)`, `rIn = 1/4`,
`rOut = 1/2`, so `χ x = 1/√chiNormSq` for `‖x‖ < 1/4`; for `‖z‖ ≤ R < ℓ/2` the cube of
half-side `t := (1/4 − R/(2ℓ))/(2√3)` centred at `z/(2ℓ)` lies inside
`ball 0 (1/4) ∩ ball (z/ℓ) (1/4)` and thus contributes `(2t)³/chiNormSq` to `(χ⋆χ)(z/ℓ)`.
-/

noncomputable section

open MeasureTheory

namespace Work.LocRepoint

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- The explicit lower bound of `convScale ℓ` on the ball of radius `R` (valid for `R < ℓ/2`). -/
noncomputable def convCubeLower (ℓ R : ℝ) : ℝ :=
  (2 * ((1 / 4 - R / (2 * ℓ)) / (2 * Real.sqrt 3))) ^ 3 / chiNormSq

/-- `convCubeLower ℓ R` is positive when `R < ℓ/2` (and `0 < ℓ`). -/
theorem convCubeLower_pos {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : R < ℓ / 2) : 0 < convCubeLower ℓ R := by
  rw [convCubeLower]
  have hden : (0 : ℝ) < 2 * Real.sqrt 3 := by positivity
  have ht : 0 < 1 / 4 - R / (2 * ℓ) := by
    have h2l : (0 : ℝ) < 2 * ℓ := by positivity
    rw [sub_pos, div_lt_iff₀ h2l]
    linarith
  exact div_pos (pow_pos (mul_pos (by norm_num) (div_pos ht hden)) 3) chiNormSq_pos

end Work.LocRepoint
