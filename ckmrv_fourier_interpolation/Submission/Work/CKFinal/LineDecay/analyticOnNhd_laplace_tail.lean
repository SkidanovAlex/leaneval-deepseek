import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs
import Submission.Work.CKFinal.LineDecay.laplace_analytic_Ici
import Submission.Work.Asymptotics.ParamIntegral
import Submission.Work.Asymptotics.paperLayer_smooth

namespace Work.CKFinal.LineDecay

/-- **Analyticity of a Laplace-type integral over a half-line.**

If `g : ℝ → ℂ` is a.e. strongly measurable and `‖g t‖ ≤ C (1+t)^N e^{-π t}` for `t ≥ 1`, then
`z ↦ ∫_{t ≥ 1} g t * exp (-(z * t)) dt` is analytic on the half plane `{z : -π < z.re}`.

Route: `Complex.analyticOnNhd_iff_differentiableOn` (the half plane is open); at `z₀` in the half
plane put `R := (z₀.re + π)/2 > 0`, whose ball is contained in the half plane; for `z ∈ ball z₀ R`
and `t ≥ 1` one has `‖g t * exp (-(z*t))‖ ≤ C (1+t)^N e^{-(π + c) t}` with
`c = (z₀.re - π)/2 > -π`, so `t ↦ ‖g t‖ e^{-ct}` and `t ↦ ‖g t‖ t e^{-ct}` are integrable on `[1,∞)`.
Apply `Work.Asymptotics.hasDerivAt_integral_Ioi` (module
`Submission.Work.Asymptotics.ParamIntegral`) to `(Set.Ici 1).indicator (fun t => g t * exp (-(z*t)))`
viewed as an integral over `Set.Ioi 0`, with the explicit derivative bound `‖g t‖ * t * e^{-Re z · t}`.
Measurability of the `z`-derivative is inherited from `hmeas` (the derivative of the integrand at
`z` is `g t * (-(t:ℂ)) * exp (-(z*t))`).  Alternatively, derive it from the already proved
`Work.Asymptotics.contDiff_omega_integral_Ici_exp` (module `Submission.Work.Asymptotics.paperLayer_smooth`)
via the substitution `z ↦ z / π`. -/
theorem analyticOnNhd_laplace_tail {g : ℝ → ℂ}
    (hmeas : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))))
    (hbound : ∃ C N : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ici (1 : ℝ),
      ‖g t‖ ≤ C * (1 + t) ^ N * Real.exp (-(Real.pi * t))) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in Set.Ici (1 : ℝ), g t * Complex.exp (-(z * (t : ℂ))))
      {z : ℂ | -(Real.pi) < z.re} := by
  -- This is the case `T = 0` of `Work.CKFinal.LineDecay.laplace_analytic_Ici`; only the exponent
  -- `N` has to be normalized to a nonnegative one, using `1 + t ≥ 1` for `t ∈ [1,∞)`.
  obtain ⟨C, N, hC, hb⟩ := hbound
  refine laplace_analytic_Ici (f := g) (C := C) (M := max N 0) (T := 0)
    hC (le_max_right _ _) le_rfl hmeas ?_
  intro t ht
  have hbase : (1 : ℝ) ≤ 1 + t := by linarith [show (1 : ℝ) ≤ t from ht]
  have hgrowth : (1 + t) ^ N ≤ (1 + t) ^ (max N 0) :=
    Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
  have hkey : C * (1 + t) ^ N * Real.exp (-(Real.pi * t))
      ≤ C * (1 + t) ^ (max N 0) * Real.exp (-(Real.pi * t)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrowth hC) (Real.exp_nonneg _)
  calc ‖g t‖ ≤ C * (1 + t) ^ N * Real.exp (-(Real.pi * t)) := hb t ht
    _ ≤ C * (1 + t) ^ (max N 0) * Real.exp (-(Real.pi * t)) := hkey
    _ = C * (1 + t) ^ (max N 0) * Real.exp (-(Real.pi * (t - 0))) := by rw [sub_zero]

end Work.CKFinal.LineDecay
