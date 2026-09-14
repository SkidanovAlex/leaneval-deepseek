import ChallengeDeps
import Submission.NBody.Scaling
import Submission.NBody.Extension

/-!
# Decay of the Newtonian force along an escaping motion

If the configuration of a motion, suitably normalized, converges to a *collision-free*
configuration `b`, then the Newtonian force decays like `t⁻²`:

    `‖∇ₘ (U m)(x t)‖ ≤ K / t²`   for all large `t`.

Indeed, for `t > 0` the configuration `x t` is the dilation by `t` of the normalized
configuration `t⁻¹ • x t`, and the mass-weighted force field is homogeneous of degree `-2`
(`weightedGrad_U_smul`), while it is bounded near the collision-free configuration `b`.

This is the estimate which makes the acceleration integrable at `+∞`, hence produces asymptotic
velocities (Chazy's lemma).

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators
open scoped Topology

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Decay of the force.**  If the normalized configuration `t⁻¹ • x t` converges to a
collision-free configuration `b`, then `‖∇ₘ (U m)(x t)‖ ≤ K / t²` eventually. -/
theorem eventually_norm_weightedGrad_le_inv_sq (m : Fin N → ℝ) {x : ℝ → EN E N} {b : EN E N}
    (hb : WithoutCollisions b) (hasym : Tendsto (fun t : ℝ => t⁻¹ • x t) atTop (𝓝 b)) :
    ∃ K : ℝ, ∀ᶠ t : ℝ in atTop, ‖weightedGrad m (U m) (x t)‖ ≤ K / t ^ 2 := by
  have hcont : ContinuousAt (fun y : EN E N => weightedGrad m (U m) y) b :=
    (contDiffAt_weightedGrad_U m b hb).continuousAt
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hcont.norm.eventually (eventually_le_nhds (lt_add_one _)))
  have hevball : ∀ᶠ t : ℝ in atTop, dist (t⁻¹ • x t) b < r :=
    (Metric.tendsto_nhds.mp hasym) r hr
  have hevnc : ∀ᶠ t : ℝ in atTop, WithoutCollisions (t⁻¹ • x t) :=
    hasym.eventually ((isOpen_setOf_withoutCollisions (E := E) (N := N)).mem_nhds hb)
  refine ⟨‖weightedGrad m (U m) b‖ + 1, ?_⟩
  filter_upwards [hevball, hevnc, eventually_gt_atTop (0 : ℝ)] with t hbdist hnc ht
  have hxt : x t = t • (t⁻¹ • x t) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]
  rw [hxt, weightedGrad_U_smul m ht (t⁻¹ • x t) hnc, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t ^ 2)⁻¹)]
  calc (t ^ 2)⁻¹ * ‖weightedGrad m (U m) (t⁻¹ • x t)‖
      ≤ (t ^ 2)⁻¹ * (‖weightedGrad m (U m) b‖ + 1) :=
        mul_le_mul_of_nonneg_left (hball hbdist) (by positivity)
    _ = (‖weightedGrad m (U m) b‖ + 1) / t ^ 2 := by rw [div_eq_inv_mul]

end Submission.NBody
