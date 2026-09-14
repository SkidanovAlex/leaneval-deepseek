import ChallengeDeps
import Submission.NBody.ForceDecay
import Submission.Commons.Analysis.Asymptotics.exists_tendsto_atTop_of_eventually_norm_le_inv_sq
import Submission.Commons.Analysis.Calculus.tendsto_smul_inv_sub_of_tendsto_deriv

/-!
# Chazy's lemma: existence of the asymptotic velocity

The acceleration of an `N`-body motion whose normalized configuration converges to a
collision-free configuration is integrable at `+∞` (`eventually_norm_weightedGrad_le_inv_sq`).
Consequently the velocity has a limit: this is the first part of Chazy's lemma.

    `x(t) = t • b + o(t)` with `b` collision-free  ⟹  `x'(t) → b`.

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

/-- **Chazy's lemma, first part.**  A solution of Newton's equations whose normalized
configuration converges to a collision-free configuration `b` has asymptotic velocity `b`. -/
theorem tendsto_deriv_of_asymptotic_config (m : Fin N → ℝ) {x : ℝ → EN E N} {b : EN E N}
    (hb : WithoutCollisions b) (h2 : ContDiffOn ℝ 2 x (Ioi (0 : ℝ)))
    (heq : ∀ t ∈ Ioi (0 : ℝ), iteratedDeriv 2 x t = weightedGrad m (U m) (x t))
    (hasym : Tendsto (fun t : ℝ => t⁻¹ • x t) atTop (𝓝 b)) :
    Tendsto (deriv x) atTop (𝓝 b) := by
  obtain ⟨K, hK⟩ := eventually_norm_weightedGrad_le_inv_sq m hb hasym
  have hderiv1 : ContDiffOn ℝ 1 (deriv x) (Ioi (0 : ℝ)) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hiter : iteratedDeriv 2 x = deriv (deriv x) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hpos : ∀ t ∈ Ici (1 : ℝ), (0 : ℝ) < t := fun t ht => lt_of_lt_of_le zero_lt_one ht
  have hxderiv : ∀ t ∈ Ici (1 : ℝ), HasDerivAt x (deriv x t) t := by
    intro t ht
    exact ((h2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hpos t ht))).hasDerivAt
  have hderiv : ∀ t ∈ Ici (1 : ℝ), HasDerivAt (deriv x) (iteratedDeriv 2 x t) t := by
    intro t ht
    rw [hiter]
    exact ((hderiv1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hpos t ht))).hasDerivAt
  have hcont : ContinuousOn (iteratedDeriv 2 x) (Ici (1 : ℝ)) := by
    rw [hiter]
    refine (hderiv1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono ?_
    intro t ht
    exact hpos t ht
  have hK' : ∀ᶠ t : ℝ in atTop, ‖iteratedDeriv 2 x t‖ ≤ K / t ^ 2 := by
    filter_upwards [hK, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    rw [heq t ht0]
    exact ht
  obtain ⟨l, hl⟩ :=
    Commons.Analysis.Asymptotics.exists_tendsto_atTop_of_eventually_norm_le_inv_sq
      (by norm_num : (0 : ℝ) < 1) hderiv hcont hK'
  have hxlim := Commons.Analysis.Calculus.tendsto_smul_inv_sub_of_tendsto_deriv (T := 1) hxderiv hl
  have hb' : Tendsto (fun t : ℝ => t⁻¹ • (x t - x 1)) atTop (𝓝 b) := by
    have h0 : Tendsto (fun t : ℝ => t⁻¹ • x 1) atTop (𝓝 (0 : EN E N)) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul (tendsto_const_nhds (x := x 1))
      simpa using h
    simpa [smul_sub, sub_zero] using hasym.sub h0
  rw [tendsto_nhds_unique hxlim hb'] at hl
  exact hl

end Submission.NBody

namespace Submission.NBody

/-- **Chazy's lemma, first part, in the paper's form.**  A solution of Newton's equations whose
configuration satisfies `x(t) = t • b + o(t)` as `t → +∞`, with `b` collision-free, has
asymptotic velocity `b`. -/
theorem tendsto_deriv_of_isLittleO (m : Fin N → ℝ) {x : ℝ → EN E N} {b : EN E N}
    {o : ℝ → EN E N} (hb : WithoutCollisions b) (h2 : ContDiffOn ℝ 2 x (Ioi (0 : ℝ)))
    (heq : ∀ t ∈ Ioi (0 : ℝ), iteratedDeriv 2 x t = weightedGrad m (U m) (x t))
    (ho : o =o[atTop] (fun t : ℝ => t))
    (hasym : ∀ᶠ t : ℝ in atTop, x t = t • b + o t) :
    Tendsto (deriv x) atTop (𝓝 b) := by
  refine tendsto_deriv_of_asymptotic_config m hb h2 heq ?_
  have hsmall : Tendsto (fun t : ℝ => t⁻¹ • o t) atTop (𝓝 (0 : EN E N)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [ho.bound (half_pos hε), eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have hnorm : ‖o t‖ ≤ (ε / 2) * t := by
      rw [Real.norm_eq_abs, abs_of_nonneg ht0.le] at ht
      simpa using ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht0)]
    calc t⁻¹ * ‖o t‖ ≤ t⁻¹ * ((ε / 2) * t) := by gcongr
      _ = ε / 2 := by
        rw [mul_comm (t⁻¹) ((ε / 2) * t), mul_assoc, mul_inv_cancel₀ (ne_of_gt ht0), mul_one]
      _ < ε := by linarith
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • x t) atTop (𝓝 b) := by
    have heq' : (fun t : ℝ => t⁻¹ • x t) =ᶠ[atTop] fun t => b + t⁻¹ • o t := by
      filter_upwards [hasym, eventually_gt_atTop (0 : ℝ)] with t ht ht0
      rw [ht, smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul]
    rw [Filter.tendsto_congr' heq']
    simpa using tendsto_const_nhds.add hsmall
  exact hlim

end Submission.NBody
