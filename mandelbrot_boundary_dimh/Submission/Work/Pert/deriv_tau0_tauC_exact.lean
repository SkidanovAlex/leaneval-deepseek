import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

/-- `τ₀ ∘ τ_f` is the entire function `z ↦ (e^{-2πiαz} - 1)/σ`.

Indeed `τ₀ w = -1/w`, so for `w = τ_f z = σ/(1 - E)` with `E = e^{-2πiαz}` we get
`τ₀ w = -(1 - E)/σ` whenever `1 - E ≠ 0`; and at the exceptional points `E = 1` both sides
vanish: `τ_f z = σ/0 = 0` and hence `τ₀ (τ_f z) = -1/0 = 0`, while `(E - 1)/σ = 0/σ = 0`.
This "removable singularity is removable exactly" coincidence is what makes the derivative
formula hold also on the zeros of `1 - e^{-2πiαz}`. -/
theorem tau0_tauC_eq (σ α z : ℂ) :
    MandelDim.tau0 (Work.Pert.tauC σ α z) =
      (Complex.exp (-(2 * Real.pi * Complex.I * α * z)) - 1) / σ := by
  rw [MandelDim.tau0, Work.Pert.tauC]
  by_cases h : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * z)) = 0
  · have hE1 : Complex.exp (-(2 * Real.pi * Complex.I * α * z)) = 1 := (sub_eq_zero.mp h).symm
    rw [h, div_zero, div_zero, hE1, sub_self, zero_div]
  · field_simp
    ring

/-- Shishikura (A.1.7)(ii): the exact chain-rule value of `(τ₀ ∘ τ_f)'(ζ)`, valid at every
`ζ ∈ ℂ` (including the points where `1 - e^{-2πiαζ} = 0`, where `τ_f` has a pole and `τ₀`
its zero, the composite being entire). -/
theorem deriv_tau0_tauC_exact {σ α ζ : ℂ} (hσ : σ ≠ 0) :
    deriv (fun z : ℂ => MandelDim.tau0 (Work.Pert.tauC σ α z)) ζ =
      -(2 * Real.pi * Complex.I * α / σ) * Complex.exp (-(2 * Real.pi * Complex.I * α * ζ)) := by
  have hfun : (fun z : ℂ => MandelDim.tau0 (Work.Pert.tauC σ α z))
      = fun z : ℂ => (Complex.exp (-(2 * Real.pi * Complex.I * α * z)) - 1) / σ :=
    funext (tau0_tauC_eq σ α)
  rw [hfun]
  -- derivative of the affine inner map `z ↦ -(2πiα z)`
  have hlin : HasDerivAt (fun z : ℂ => -(2 * Real.pi * Complex.I * α * z))
      (-(2 * Real.pi * Complex.I * α)) ζ :=
    (hasDerivAt_const_mul (2 * Real.pi * Complex.I * α) (x := ζ)).neg
  -- chain rule with `Complex.exp`
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (-(2 * Real.pi * Complex.I * α * z)))
      (Complex.exp (-(2 * Real.pi * Complex.I * α * ζ)) * (-(2 * Real.pi * Complex.I * α))) ζ :=
    (Complex.hasDerivAt_exp (-(2 * Real.pi * Complex.I * α * ζ))).comp ζ hlin
  -- subtract the constant `1` and divide by `σ`
  have hres := (hexp.sub_const (1 : ℂ)).div_const σ
  rw [hres.deriv]
  ring

end Work.Pert
