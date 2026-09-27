import Mathlib
import Submission.Work.Drive.haReduction
import Submission.Work.Drive.clampedSweepLevel

/-!
# The radial non-degeneracy `ha` for the clamped sweeps, from the level choice

`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes` carries the radial
non-degeneracy

> `ha : deriv ψ (x k 2) · (log (c k) − log (levelOf (P k (x k 0, x k 1)))) ≠ 0`  at every triple point,

as one of its four plane-local/geometric inputs.  `Work.Drive.ha_of_deriv_ne_of_level_ne`
(`haReduction.lean`) reduces it to `deriv ψ ≠ 0` on `[0,1]` together with `levelOf (P k y) ≠ c k` for
*every* parameter `y`.  This file discharges the second half from the level choice of the endgame
(`c 0 < levelOf (P k y)` for the three planes, with `c 0` the largest truncation level), so that the
only remaining content of `ha` is the choice of the sweep profile (`ψ t = 1 - t` works, and its
derivative is `-1`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **`ha` for the clamped sweeps, from the profile and the level choice.** -/
theorem ha_clampedSweeps (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ)
    (ψ : ℝ → ℝ) (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hψ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv ψ t ≠ 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y)) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) →
      clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) →
      ∀ k, deriv ψ (x k 2) * (Real.log (c k)
        - Real.log (levelOf (P k (mk2 (x k 0) (x k 1))))) ≠ 0 := by
  refine ha_of_deriv_ne_of_level_ne P c ψ hψ' hcpos (fun k y h => ?_)
  exact absurd h (ne_of_gt (lt_of_le_of_lt (hck k) (hlev k y)))

end

end Work.Drive
