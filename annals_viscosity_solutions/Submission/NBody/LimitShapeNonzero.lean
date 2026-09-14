import Submission.NBody.LimitShape
import Submission.NBody.CollisionFreeLimit
import Submission.NBody.Jacobi
import Submission.NBody.EnergyAsymptotic
import Submission.Commons.Analysis.Calculus.exists_quadratic_le_of_iteratedDeriv_two_ge

/-!
# The limit shape does not vanish

A motion `γ` with positive energy `h` whose normalized configuration converges to `b` cannot have
`b = 0`: by the Lagrange--Jacobi identity the inertia `I = ∑ mᵢ‖γᵢ‖²` satisfies
`I'' = 4E + 2U ≥ 4h > 0`, so `I(t) ≥ h t²` for all large `t`
(`Commons.Analysis.Calculus.exists_quadratic_le_of_iteratedDeriv_two_ge`), whereas `b = 0` would
force `I(t) = o(t²)`.  This is the paper's justification (`b = 0` forces `h = 0`) of the fact that
the limit shape of a hyperbolic motion is a *direction*.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}
variable [Nontrivial E]

namespace Submission.NBody

theorem limitShape_ne_zero {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {b : EN E N}
    (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hsol : IsNBodySolution m γ) (hnc : ∀ t > 0, WithoutCollisions (γ t))
    (henergy : ∀ t > 0, energy m γ t = h)
    (hshape : Tendsto (fun t : ℝ => t⁻¹ • γ t) atTop (𝓝 b)) :
    b ≠ 0 := by
  intro hb
  -- the second derivative of the inertia is `≥ 4h`
  have h2 : ∀ t ∈ Set.Ioi (0 : ℝ), 4 * h ≤ iteratedDeriv 2 (inertia m γ) t := by
    intro t ht
    rw [iteratedDeriv_two_inertia m (fun i => (hm i).ne') hsol hnc ht, henergy t ht]
    have := U_nonneg (fun i => (hm i).le) (γ t)
    linarith
  obtain ⟨T, hT⟩ := Commons.Analysis.Calculus.exists_quadratic_le_of_iteratedDeriv_two_ge hh (contDiffOn_inertia m hsol.contDiff) h2
  -- but `b = 0` makes the inertia `o(t²)`
  have hsmall : ∀ᶠ t : ℝ in atTop, inertia m γ t < h * t ^ 2 := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹ • γ t) atTop (𝓝 (0 : EN E N)) := by
      rw [← hb]; exact hshape
    have hSpos : 0 < ∑ i, m i := sum_mass_pos hm ⟨0, hN⟩
    set cc : ℝ := Real.sqrt h / Real.sqrt (∑ i, m i) with hccdef
    have hccpos : 0 < cc := by
      rw [hccdef]
      exact div_pos (Real.sqrt_pos.mpr hh) (Real.sqrt_pos.mpr hSpos)
    have h2 : ∀ᶠ t : ℝ in atTop, ‖t⁻¹ • γ t‖ < cc := by
      have h3 := (Metric.tendsto_nhds.mp h1) cc hccpos
      filter_upwards [h3] with t ht
      rwa [dist_zero_right] at ht
    filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have h4 : ‖γ t‖ < cc * t := by
      have h5 : ‖t⁻¹ • γ t‖ = t⁻¹ * ‖γ t‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
      rw [h5] at ht
      calc ‖γ t‖ = t * (t⁻¹ * ‖γ t‖) := by field_simp
        _ < t * cc := mul_lt_mul_of_pos_left ht ht0
        _ = cc * t := by ring
    have h6 : inertia m γ t ≤ (∑ i, m i) * ‖γ t‖ ^ 2 := by
      rw [inertia]
      calc ∑ i, m i * ‖γ t i‖ ^ 2 ≤ ∑ i, m i * ‖γ t‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (hm i).le
            have h7 : ‖γ t i‖ ≤ ‖γ t‖ := PiLp.norm_apply_le _ _
            nlinarith [norm_nonneg (γ t i), norm_nonneg (γ t)]
        _ = (∑ i, m i) * ‖γ t‖ ^ 2 := by rw [Finset.sum_mul]
    calc inertia m γ t ≤ (∑ i, m i) * ‖γ t‖ ^ 2 := h6
      _ < (∑ i, m i) * (cc * t) ^ 2 := by
          refine mul_lt_mul_of_pos_left ?_ hSpos
          nlinarith [h4, norm_nonneg (γ t), hccpos, ht0]
      _ = h * t ^ 2 := by
          rw [hccdef, mul_pow, div_pow, Real.sq_sqrt hh.le, Real.sq_sqrt hSpos.le]
          field_simp
  obtain ⟨T', hT'⟩ := eventually_atTop.1 hsmall
  have h1 := hT (max T T') (le_max_left _ _)
  have h2' := hT' (max T T') (le_max_right _ _)
  linarith


end Submission.NBody
