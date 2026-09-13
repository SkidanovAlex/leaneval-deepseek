/-
# Passing the interior gradient estimate to locally uniform limits of classical solutions

Continues `Submission/SmoothGradientWeighted.lean`.  The closure step of the passage from classical
solutions to viscosity solutions in Trudinger--Wang's weighted interior gradient estimate:

* `Submission.lipschitzOn_of_tendsto` — a pointwise limit of `K`-Lipschitz functions is
  `K`-Lipschitz;
* `Submission.norm_fderiv_le_of_tendsto_lipschitzOn` — hence the derivative at a point is bounded
  by `K`;
* `Submission.norm_fderiv_le_of_tendsto_lipschitzOn` — the derivative at a point of such a limit.

(The uniform Lipschitz bound for smooth solutions on the half ball, and the resulting estimate for
a pointwise limit of classical solutions, are stated in `Submission/SmoothGradientCenter.lean`
(`Submission.lipschitzOn_smooth_of_sigma2`) resp. recorded in `Submission/Roadmap.md`; the direct
`∃ C`-formulations caused a Lean elaboration blow-up, see the traps there.)
-/
import Mathlib
import Submission.SmoothGradientWeighted

open HessianEstimates
open Laplacian Metric MeasureTheory Filter
open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- A pointwise limit of `K`-Lipschitz functions is `K`-Lipschitz. -/
theorem lipschitzOn_of_tendsto {g : ℝ⁴ → ℝ} {u : ℕ → ℝ⁴ → ℝ} {s : Set ℝ⁴} {K : ℝ}
    (hlip : ∀ n y z, y ∈ s → z ∈ s → |u n y - u n z| ≤ K * dist y z)
    (htend : ∀ x ∈ s, Tendsto (fun n => u n x) atTop (𝓝 (g x))) :
    ∀ y ∈ s, ∀ z ∈ s, |g y - g z| ≤ K * dist y z := by
  intro y hy z hz
  have hconv : Tendsto (fun n => |u n y - u n z|) atTop (𝓝 |g y - g z|) :=
    ((htend y hy).sub (htend z hz)).abs
  exact le_of_tendsto hconv (Eventually.of_forall fun n => hlip n y z hy hz)

/-- The derivative at a point of a pointwise limit of `K`-Lipschitz functions is bounded by `K`. -/
theorem norm_fderiv_le_of_tendsto_lipschitzOn {g : ℝ⁴ → ℝ} {u : ℕ → ℝ⁴ → ℝ} {s : Set ℝ⁴} {K : ℝ}
    {c : ℝ⁴} (hK : 0 ≤ K) (hs : s ∈ 𝓝 c)
    (hlip : ∀ n y z, y ∈ s → z ∈ s → |u n y - u n z| ≤ K * dist y z)
    (htend : ∀ x ∈ s, Tendsto (fun n => u n x) atTop (𝓝 (g x))) :
    ‖fderiv ℝ g c‖ ≤ K := by
  have hlip' : ∀ᶠ x in 𝓝 c, ‖g x - g c‖ ≤ K * ‖x - c‖ := by
    filter_upwards [hs] with x hx
    have h1 := lipschitzOn_of_tendsto hlip htend x hx c (mem_of_mem_nhds hs)
    rw [dist_eq_norm] at h1
    rw [Real.norm_eq_abs]
    exact h1
  exact norm_fderiv_le_of_lip' ℝ hK hlip'

end Submission
