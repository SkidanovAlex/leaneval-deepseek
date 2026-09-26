import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.Kaxis_bounded_compact
import Submission.Work.Asymptotics.cuspExpansionKernel
import Submission.Work.LayerCont.AexpLow
import Submission.Work.LayerCont.TailIntegrable

/-!
# The truncated contour integrand is dominated near a point of `𝒟`

`Work.CKFinal.AxisCont.trunc_integrand_dominated` provides, for a fixed `τ₁ ∈ 𝒟 = DomainD`
(the CKMRV fundamental domain of `Γ(2)`), a ball around `τ₁` and a single function of `t`,
integrable on `[1,∞)`, dominating the Gaussian-damped trunc integrand
`(K^{(d)}(τ,it) - 𝒢(τ,it))·e^{-πr²t}` uniformly in `τ` in that ball.

The mathematics is the CKMRV cusp-`i∞` expansion of the kernel along the contour,
`Work.Asymptotics.cuspExpansionKernel`: for every compact `K ⊆ 𝒟`,

  `‖K^{(d)}(τ,it) - 𝒢(τ,it)‖ ≤ C (1+t)^M e^{-π(t-T₀)}`  (`τ ∈ K`, `t ≥ 1`),

with constants uniform on `K`.  Since `𝒟` is open, a sufficiently small `closedBall τ₁ ρ`
is compact and contained in `𝒟`; multiplying the expansion by `|e^{-πr²t}| = e^{-πr²t}` and
combining the exponentials gives the majorant

  `(C e^{πT₀}) · (1+t)^M · e^{-π(1+r²)t}`,

which is integrable on `[1,∞)` because `π(1+r²) > 0`
(`Work.LayerCont.TailIntegrable`). -/

namespace Work.CKFinal.AxisCont

open MeasureTheory

theorem trunc_integrand_dominated (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ₁ : UpperHalfPlane} (hτ₁ : τ₁ ∈ Work.Asymptotics.DomainD) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ bound : ℝ → ℝ,
      MeasureTheory.Integrable bound (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Metric.closedBall τ₁ ρ → 1 ≤ t →
        ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ bound t := by
  -- `𝒟` is open, so a small Euclidean ball around `τ₁` is compact and inside `𝒟`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Work.Asymptotics.isOpen_DomainD τ₁ hτ₁
  set ρ : ℝ := ε / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hsub : Metric.closedBall τ₁ ρ ⊆ Work.Asymptotics.DomainD :=
    (Metric.closedBall_subset_ball (by rw [hρdef]; linarith)).trans hball
  -- the uniform cusp-`i∞` expansion of the kernel on this compact piece of `𝒟`
  obtain ⟨C, M, T₀, _hC, hM, _hT₀, hb⟩ :=
    Work.Asymptotics.cuspExpansionKernel ℓ d hd (isCompact_closedBall τ₁ ρ) hsub
  set bound : ℝ → ℝ := fun t => (C * Real.exp (Real.pi * T₀)) *
      ((1 + t) ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) with hbounddef
  have ha : 0 < Real.pi * (1 + r ^ 2) := by positivity
  have hbndint : MeasureTheory.Integrable bound
      (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hbounddef]
    exact (Work.LayerCont.TailIntegrable hM ha).const_mul _
  refine ⟨ρ, hρ, bound, hbndint, ?_⟩
  intro τ t hτ ht
  have hbτ := hb τ t hτ ht
  -- the Gaussian factor is a real exponential
  have harg : (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
      = Real.exp (-(Real.pi * r ^ 2 * t)) := by
    rw [harg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  -- combining `e^{-π(t-T₀)}` with `e^{-πr²t}` gives `e^{πT₀}·e^{-π(1+r²)t}`
  have hexp : Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
      = Real.exp (Real.pi * T₀) * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)) := by
    have h1 : -(Real.pi * (t - T₀)) + -(Real.pi * r ^ 2 * t)
        = Real.pi * T₀ + -((Real.pi * (1 + r ^ 2)) * t) := by ring
    calc Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
        = Real.exp (-(Real.pi * (t - T₀)) + -(Real.pi * r ^ 2 * t)) :=
          (Real.exp_add _ _).symm
      _ = Real.exp (Real.pi * T₀ + -((Real.pi * (1 + r ^ 2)) * t)) := by rw [h1]
      _ = Real.exp (Real.pi * T₀) * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)) :=
          Real.exp_add _ _
  rw [norm_mul, hnorm]
  refine le_trans (mul_le_mul_of_nonneg_right hbτ (Real.exp_pos _).le) (le_of_eq ?_)
  calc (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
        * Real.exp (-(Real.pi * r ^ 2 * t))
      = C * ((1 + t) ^ M * (Real.exp (-(Real.pi * (t - T₀)))
          * Real.exp (-(Real.pi * r ^ 2 * t)))) := by ring
    _ = C * ((1 + t) ^ M * (Real.exp (Real.pi * T₀)
          * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)))) := by rw [hexp]
    _ = bound t := by simp only [hbounddef]; ring

end Work.CKFinal.AxisCont
