import Mathlib
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.funnelTailBasic

/-!
# The `j(τ)·Θ₀` bound

`‖j(τ)·Θ₀(τ,z)‖ = O(‖q(τ)‖⁻¹ · scale τ)` on the funnel strip.  The prefactor
`(‖q(τ)‖)⁻¹ = exp(2π·Im τ)` exactly cancels the exponential growth of `j(τ)`, so the content is
the product of the two proved bounds

* `K24Fsm.th0_le`: `‖Θ₀(τ,z)‖ ≤ CΘ·scale τ` (for `Funnel τ`, `3 ≤ Im z`), and
* `exists_jInvariantFun_Funnel_bound`: `‖j(τ)‖ ≤ Cj·exp(2π·Im τ)`.

On the strip `τ.im + 1 ≤ t = z.im` with `τ ∈ 𝔽` one has `z.im ≥ 3`, which is precisely
`th0_le`'s hypothesis (and `|z| ≥ 3` is what keeps `S0z z` bounded inside it).  This is the
input that, together with `dDelta_bound`, gives `dSm5 = -(dDelta·j(τ))·Θ₀ = O(q³·scale)`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **`j(τ)·Θ₀(τ,z) = O(‖q(τ)‖⁻¹ · scale τ)`** on the funnel strip. -/
theorem JTheta0Bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ →
        UpperHalfPlane.im τ + 1 ≤ t →
        0 ≤ UpperHalfPlane.re z → UpperHalfPlane.re z ≤ 1 → UpperHalfPlane.im z = t →
        ‖Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z‖
          ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ N
              * (1 + t) ^ M := by
  obtain ⟨Cj, hCj, hj⟩ := Work.Asymptotics.exists_jInvariantFun_Funnel_bound
  obtain ⟨Ct, hCt, ht⟩ := Work.Asymptotics.K24Fsm.th0_le
  refine ⟨Cj * Ct, 1, 0, by positivity, by norm_num, by norm_num,
    fun τ z t hF ht' hz0 hz1 hzim => ?_⟩
  have hz3 : (3 : ℝ) ≤ UpperHalfPlane.im z := by
    have h2 : (2 : ℝ) ≤ UpperHalfPlane.im τ := hF.2
    rw [hzim]
    linarith
  have h1 := hj τ hF
  have h2 := ht τ z hF hz3
  have hq : (‖Work.Kernels.qParamFun τ‖)⁻¹ = Real.exp (2 * Real.pi * UpperHalfPlane.im τ) := by
    rw [Work.Asymptotics.norm_qParamFun, ← Real.exp_neg, neg_neg]
  rw [norm_mul, hq, Real.rpow_one, Real.rpow_zero, mul_one]
  calc ‖Work.Kernels.jInvariantFun τ‖ * ‖Work.Asymptotics.K24F.Th0 τ z‖
      ≤ (Cj * Real.exp (2 * Real.pi * UpperHalfPlane.im τ))
          * (Ct * Work.Kernels.scale τ) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = Cj * Ct * Real.exp (2 * Real.pi * UpperHalfPlane.im τ)
          * Work.Kernels.scale τ := by ring

end

end Work.Asymptotics.KhatE1Core
