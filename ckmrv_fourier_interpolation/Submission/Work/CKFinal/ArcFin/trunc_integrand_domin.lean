import Mathlib
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.LayerCont.TailIntegrable

namespace Work.CKFinal.ArcFin

/-- If `hdom` bounds the truncation error `Kaxis - Aexp` by `C (1+t)^M e^{-π(t-T₀)}`, then
the same error multiplied by the Fourier kernel `e^{-π r² t}` is dominated by the
integrable function `(C e^{π T₀}) (1+t)^M e^{-π(1+r²) t}`. -/
theorem trunc_integrand_domin (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ)
    {τ₀ : UpperHalfPlane} {ρ C M T₀ : ℝ} (hρ : 0 < ρ) (hC : 0 < C) (hM : 0 ≤ M) (hT₀ : 0 ≤ T₀)
    (hdom : ∀ τ : UpperHalfPlane, τ ∈ Metric.closedBall τ₀ ρ → ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    MeasureTheory.Integrable (fun t : ℝ => (C * Real.exp (Real.pi * T₀))
        * ((1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t))))
      (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) ∧
    (∀ τ : UpperHalfPlane, τ ∈ Metric.closedBall τ₀ ρ → ∀ t : ℝ, 1 ≤ t →
      ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ (C * Real.exp (Real.pi * T₀))
            * ((1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t)))) := by
  -- Exponent bookkeeping: the Fourier kernel `e^{-πr²t}` has modulus `e^{-πr²t}`.
  have hnorm_exp : ∀ t : ℝ,
      ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
    intro t
    rw [Complex.norm_exp]
    have hre : (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))).re = -(Real.pi * r ^ 2 * t) := by
      rw [show -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) by
            push_cast; ring, Complex.ofReal_re]
    rw [hre]
  -- The product identity relating the two displayed forms.
  have hmul : ∀ t : ℝ,
      (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) * Real.exp (-(Real.pi * r ^ 2 * t))
      = (C * Real.exp (Real.pi * T₀))
          * ((1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) := by
    intro t
    have hexp : Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
        = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * (1 + r ^ 2) * t)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) * Real.exp (-(Real.pi * r ^ 2 * t))
        = C * (1 + t) ^ M
            * (Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))) := by ring
      _ = C * (1 + t) ^ M
            * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) := by rw [hexp]
      _ = (C * Real.exp (Real.pi * T₀))
            * ((1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) := by ring
  refine ⟨?_, ?_⟩
  · -- Integrability of the dominating function over `[1,∞)`.
    have ha : 0 < Real.pi * (1 + r ^ 2) := by positivity
    have hbase := Work.LayerCont.TailIntegrable (M := M) (a := Real.pi * (1 + r ^ 2)) hM ha
    exact hbase.const_mul (C * Real.exp (Real.pi * T₀))
  · -- Pointwise domination.
    intro τ hτ t ht
    have h1 := hdom τ hτ t ht
    rw [norm_mul, hnorm_exp t]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
            * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
            * Real.exp (-(Real.pi * r ^ 2 * t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = (C * Real.exp (Real.pi * T₀))
            * ((1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) := hmul t

end Work.CKFinal.ArcFin
