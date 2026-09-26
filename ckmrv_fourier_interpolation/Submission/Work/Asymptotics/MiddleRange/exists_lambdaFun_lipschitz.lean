import Mathlib
import Submission.Work.Rigidity.lambda_local_inverse
import Submission.Work.Rigidity.lambda_fiber_orbit

namespace Work.Asymptotics.MiddleRange

/-- **A strict derivative gives a local lower Lipschitz bound.**  If `f : ℂ → ℂ` is strictly
differentiable at `x` with derivative `f' ≠ 0`, then in a neighbourhood of `x` the map `f`
strictly expands distances: `c ‖y - z‖ ≤ ‖f y - f z‖` for some `c > 0`.

This is the analytic core of the local bi-Lipschitzianity of `λ`: strict differentiability at
`x` means that `f y - f z - f' (y - z) = o(y - z)` *uniformly* as `y, z → x` jointly, and the
reverse triangle inequality then gives the bound with `c = ‖f'‖ / 2`. -/
lemma exists_lipschitz_lower_bound_of_hasStrictDerivAt {f : ℂ → ℂ} {x : ℂ} {f' : ℂ}
    (h : HasStrictDerivAt f f' x) (hf' : f' ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧ ∀ y z : ℂ, ‖y - x‖ < ρ → ‖z - x‖ < ρ →
      c * ‖y - z‖ ≤ ‖f y - f z‖ := by
  have hlo := h.hasStrictFDerivAt.isLittleO
  have hf'pos : 0 < ‖f'‖ := norm_pos_iff.mpr hf'
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp
    (hlo.bound (by linarith : (0:ℝ) < ‖f'‖ / 2))
  refine ⟨δ, hδpos, ‖f'‖ / 2, by linarith, ?_⟩
  intro y z hy hz
  have hy' : dist y x < δ := by rw [dist_eq_norm]; exact hy
  have hz' : dist z x < δ := by rw [dist_eq_norm]; exact hz
  have hpair : dist (y, z) (x, x) < δ := by
    rw [Prod.dist_eq]; exact max_lt hy' hz'
  have hb := hδ hpair
  have hB : ‖(ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖ = ‖f'‖ * ‖y - z‖ := by
    rw [ContinuousLinearMap.toSpanSingleton_apply, norm_smul, mul_comm]
  have h2 : (f y - f z) - ((f y - f z) - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z))
      = (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z) := by abel
  have h1 : ‖(ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖
      ≤ ‖f y - f z‖ + ‖f y - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖ := by
    calc ‖(ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖
        = ‖(f y - f z) - ((f y - f z) - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z))‖
          := (congrArg (fun w : ℂ => ‖w‖) h2).symm
      _ ≤ ‖f y - f z‖ + ‖f y - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖
          := norm_sub_le _ _
  have key : ‖f'‖ * ‖y - z‖ ≤ ‖f y - f z‖ + ‖f'‖ / 2 * ‖y - z‖ := by
    rw [← hB]
    exact le_trans h1 (add_le_add_right hb _)
  linarith

/-- **`λ` is locally bi-Lipschitz.**  Near every point `τ₀ ∈ ℍ` the modular lambda function
`λ = θ₁₀⁴/θ₀₀⁴` expands Euclidean distances: it is injective on a small ball and
`c ‖τ - z‖ ≤ ‖λ τ - λ z‖` there.  (`λ` is a local biholomorphism, and its derivative
`λ' = π i λ (1-λ) θ₀₀⁴` vanishes nowhere: `Work.Rigidity.lambda_local_inverse`.) -/
theorem exists_lambdaFun_lipschitz (τ₀ : UpperHalfPlane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧ ∀ τ z : UpperHalfPlane,
      ‖(τ : ℂ) - (τ₀ : ℂ)‖ < ρ → ‖(z : ℂ) - (τ₀ : ℂ)‖ < ρ →
      c * ‖(τ : ℂ) - (z : ℂ)‖ ≤ ‖Work.Kernels.lambdaFun τ - Work.Kernels.lambdaFun z‖ := by
  obtain ⟨c₀, hc₀⟩ := Work.Rigidity.exists_rho_const
  have hc₀ne : c₀ ≠ 0 := Work.Rigidity.rho_const_ne_zero hc₀
  have hdne : deriv Work.Kernels.LogLambda.lamC (τ₀ : ℂ) ≠ 0 := by
    rw [Work.Rigidity.deriv_lamC_eq_const hc₀ (τ₀ : ℂ) τ₀.im_pos]
    exact mul_ne_zero hc₀ne (Work.Rigidity.rhoC_denom_ne_zero (τ₀ : ℂ) τ₀.im_pos)
  have hAna : AnalyticAt ℂ Work.Kernels.LogLambda.lamC (τ₀ : ℂ) :=
    Work.Kernels.LogLambda.differentiableOn_lamC.analyticAt
      (Work.Kernels.LogLambda.isOpen_U.mem_nhds τ₀.im_pos)
  obtain ⟨ρ, hρpos, c, hcpos, h⟩ :=
    exists_lipschitz_lower_bound_of_hasStrictDerivAt hAna.hasStrictDerivAt hdne
  refine ⟨ρ, hρpos, c, hcpos, fun τ z hτ hz => ?_⟩
  have h1 := h (τ : ℂ) (z : ℂ) hτ hz
  rw [Work.Rigidity.lamC_coe τ, Work.Rigidity.lamC_coe z] at h1
  exact h1

end Work.Asymptotics.MiddleRange
