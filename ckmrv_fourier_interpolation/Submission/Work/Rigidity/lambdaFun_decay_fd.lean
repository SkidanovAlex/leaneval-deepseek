/-
# Decay of the modular lambda function at the cusp of the fundamental domain

`λ = θ₁₀⁴/θ₀₀⁴` vanishes at the cusp `i∞`.  Here we record the quantitative form
needed by the rigidity arguments: on the standard fundamental domain `fd` the value
`‖λ z‖` is bounded by a constant times `exp (-π Im z)`, and on `fd` the imaginary part
controls the modulus, `√3/2 · ‖z‖ ≤ Im z` as soon as `‖z‖ ≥ 1`.  Combining the two
gives `∀ ε > 0, ∃ R, ∀ z ∈ fd, R ≤ ‖z‖ → ‖λ z‖ ≤ ε`.
-/
import Mathlib
import Submission.Work.Modular.theta2_at_cusp
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_re_bound

noncomputable section

open Filter Topology
open scoped Topology UpperHalfPlane
open Work.Kernels

namespace Work.Rigidity

/-- On the fundamental domain, `‖θ₁₀‖` is bounded by `3 e^{-π Im τ/4}`. -/
private lemma norm_theta10Fun_le_exp_fd (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    ‖theta10Fun τ‖ ≤ 3 * Real.exp (-(Real.pi * τ.im / 4)) := by
  obtain ⟨-, hup⟩ := Work.Kernels.LogLambda.LogGrowth.ratio_norm_bounds_fd τ hτ
  have htheta : ‖theta10Fun τ‖
      = Real.exp (-(Real.pi * τ.im / 4)) * ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ := by
    simp only [theta10Fun]
    rw [norm_mul, Work.Kernels.LogLambda.LogGrowth.norm_exp_pi_I_div_four]
  rw [htheta]
  have he : 0 ≤ Real.exp (-(Real.pi * τ.im / 4)) := Real.exp_nonneg _
  nlinarith

/-- On the fundamental domain, `λ = θ₁₀⁴/θ₀₀⁴` is controlled by `θ₁₀`. -/
private lemma norm_lambdaFun_le_fd (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    ‖lambdaFun τ‖ ≤ 16 * ‖theta10Fun τ‖ ^ 4 := by
  have h0 : (1 / 2 : ℝ) ≤ ‖theta00Fun τ‖ :=
    Work.Kernels.LogLambda.LogGrowth.theta00Fun_fd_lower τ hτ
  have h4 : (1 / 2 : ℝ) ^ 4 ≤ ‖theta00Fun τ‖ ^ 4 :=
    pow_le_pow_left₀ (by norm_num) h0 4
  have hnn : (0 : ℝ) ≤ ‖theta10Fun τ‖ := norm_nonneg _
  rw [lambdaFun, VFun, UFun, norm_div, norm_pow, norm_pow]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖theta00Fun τ‖ ^ 4)]
  nlinarith [pow_nonneg hnn 4, h4]

/-- Quantitative decay of `λ` on the fundamental domain. -/
private lemma norm_lambdaFun_le_exp_fd (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    ‖lambdaFun τ‖ ≤ 1296 * Real.exp (-(Real.pi * τ.im)) := by
  have h1 := norm_lambdaFun_le_fd τ hτ
  have h2 := norm_theta10Fun_le_exp_fd τ hτ
  have h2' : ‖theta10Fun τ‖ ^ 4 ≤ (3 * Real.exp (-(Real.pi * τ.im / 4))) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 4
  have hexp : (3 * Real.exp (-(Real.pi * τ.im / 4))) ^ 4
      = 81 * Real.exp (-(Real.pi * τ.im)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num
    ring
  calc ‖lambdaFun τ‖ ≤ 16 * ‖theta10Fun τ‖ ^ 4 := h1
    _ ≤ 16 * (3 * Real.exp (-(Real.pi * τ.im / 4))) ^ 4 := by linarith
    _ = 16 * (81 * Real.exp (-(Real.pi * τ.im))) := by rw [hexp]
    _ = 1296 * Real.exp (-(Real.pi * τ.im)) := by ring

/-- On `fd`, once `‖z‖ ≥ 1` the imaginary part dominates: `√3/2 · ‖z‖ ≤ Im z`. -/
private lemma sqrt3_div_two_mul_norm_le_im (z : ℍ) (hz : z ∈ ModularGroup.fd)
    (h1 : 1 ≤ ‖(z : ℂ)‖) : Real.sqrt 3 / 2 * ‖(z : ℂ)‖ ≤ z.im := by
  have hsq : ‖(z : ℂ)‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  have hre : |z.re| ≤ 1 / 2 := hz.2
  have hx : z.re ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.mp hre]
  have htarget : (Real.sqrt 3 / 2 * ‖(z : ℂ)‖) ^ 2 ≤ z.im ^ 2 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h4 : (Real.sqrt 3 / 2 * ‖(z : ℂ)‖) ^ 2 = 3 / 4 * ‖(z : ℂ)‖ ^ 2 := by
      rw [mul_pow, div_pow, h3]; ring
    rw [h4, hsq]
    nlinarith [hx, h1]
  have himnn : 0 ≤ Real.sqrt 3 / 2 * ‖(z : ℂ)‖ := by positivity
  have hs := sq_le_sq.mp htarget
  rwa [abs_of_nonneg himnn, abs_of_nonneg (le_of_lt z.im_pos)] at hs

/-- **Decay of `λ` on the fundamental domain.** For every `ε > 0` there is `R` such that
on `ModularGroup.fd` the modulus `‖λ z‖` is at most `ε` once `‖z‖ ≥ R`. -/
theorem lambdaFun_decay_fd :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : UpperHalfPlane, z ∈ ModularGroup.fd →
      R ≤ ‖(z : ℂ)‖ → ‖Work.Kernels.lambdaFun z‖ ≤ ε := by
  intro ε hε
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      1296 * Real.exp (-(Real.pi * (Real.sqrt 3 / 2) * r)) < ε := by
    have hc : 0 < Real.pi * (Real.sqrt 3 / 2) := by positivity
    have hlin : Filter.Tendsto (fun r : ℝ => Real.pi * (Real.sqrt 3 / 2) * r)
        Filter.atTop Filter.atTop := Filter.tendsto_id.const_mul_atTop hc
    have hexp : Filter.Tendsto (fun r : ℝ => Real.exp (-(Real.pi * (Real.sqrt 3 / 2) * r)))
        Filter.atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    have h1296 : Filter.Tendsto (fun r : ℝ => 1296 * Real.exp (-(Real.pi * (Real.sqrt 3 / 2) * r)))
        Filter.atTop (nhds (1296 * 0)) := hexp.const_mul 1296
    rw [mul_zero] at h1296
    exact Filter.eventually_atTop.1 ((tendsto_order.1 h1296).2 ε hε)
  refine ⟨max R 1, ?_⟩
  intro z hz hzR
  have hRle : R ≤ ‖(z : ℂ)‖ := le_trans (le_max_left _ _) hzR
  have h1le : 1 ≤ ‖(z : ℂ)‖ := le_trans (le_max_right _ _) hzR
  have hbd := norm_lambdaFun_le_exp_fd z hz
  have him := sqrt3_div_two_mul_norm_le_im z hz h1le
  have hmul : Real.pi * (Real.sqrt 3 / 2 * ‖(z : ℂ)‖) ≤ Real.pi * z.im :=
    mul_le_mul_of_nonneg_left him Real.pi_pos.le
  have hmul' : (Real.pi * (Real.sqrt 3 / 2)) * ‖(z : ℂ)‖ ≤ Real.pi * z.im := by
    rw [mul_assoc]; exact hmul
  have hexp : Real.exp (-(Real.pi * z.im))
      ≤ Real.exp (-(Real.pi * (Real.sqrt 3 / 2) * ‖(z : ℂ)‖)) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc ‖Work.Kernels.lambdaFun z‖ ≤ 1296 * Real.exp (-(Real.pi * z.im)) := hbd
    _ ≤ 1296 * Real.exp (-(Real.pi * (Real.sqrt 3 / 2) * ‖(z : ℂ)‖)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ ε := le_of_lt (hR _ hRle)

end Work.Rigidity
