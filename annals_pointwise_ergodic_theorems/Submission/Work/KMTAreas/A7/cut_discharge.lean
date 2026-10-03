/-
# The cutoffs `m_*`, `m̃_*` are `1` near the origin

The model side of the §6 single-scale estimate carries the cutoffs `mStarF U = η_{≤ -2U}`,
`mStargF d U = η_{≤ -2dU}` with `U = uScale ρ L`; on the ball `|θ| ≤ 2^{-2U}/2` (resp.
`|θ| ≤ 2^{-2dU}/2`) these equal `1` by `kmtEta_one`.  Since the supports of the bumps are
`|θ| ≤ 2^{k - Log N}` (`varphiNt_support_le_all`, `varphitildeNt_support_all`), the cutoffs may be
dropped from the model integral under the band condition `k + 2U ≤ Log N - 1` — the hypothesis
`hcut₁`/`hcut₂` of `Work.KMTAreas.A7.hiKdiff_fibreSum`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.HiFibreDefs
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all
import Submission.Work.KMTAreas.A7.varphiNt_bounds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTContract

/-- **The cutoff `m_*` is `1` on the ball of radius `2^{-2U}/2`.** -/
theorem mStarF_eq_one_of_abs_le {U : ℕ} {θ : ℝ}
    (hθ : |θ| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ))) / 2) : mStarF U θ = 1 := by
  rw [mStarF, etaCut]
  refine Work.KMTContract.kmtEta_one ?_
  rw [abs_div]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := by positivity
  rw [abs_of_pos hpos, div_le_iff₀ hpos]
  linarith

/-- **The cutoff `m̃_*` is `1` on the ball of radius `2^{-2dU}/2`.** -/
theorem mStargF_eq_one_of_abs_le {d U : ℕ} {θ : ℝ}
    (hθ : |θ| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) / 2) : mStargF d U θ = 1 := by
  rw [mStargF, etaCut]
  refine Work.KMTContract.kmtEta_one ?_
  rw [abs_div]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) := by positivity
  rw [abs_of_pos hpos, div_le_iff₀ hpos]
  linarith

end

end Work.KMTAreas.A7
