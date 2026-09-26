import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.Kernels.Theorem31
import Submission.Work.FunctionalEquations.KernelSampleValues

/-!
# Sample values of the derivatives of the generating functions `F = Fgen K`, `F̃ = Ftgen K̂`

Companion of `Work.FunctionalEquations.KernelSampleValues`.  With

  `F(τ, r) = e^{π i τ r²} + 4 sin²(π r² / 2) ∫_0^∞ K(τ, it) e^{-π r² t} dt`

the sine factor `4 sin²(π r²/2)` vanishes to *second order* at the sample radius
`r_m = √(2m)`: both its value and its derivative vanish there.  Hence the derivative of the
whole kernel term vanishes at `r_m`, and the derivative of `F` is that of the Gaussian term
`e^{π i τ r²}`, namely `2 π i τ r_m · e^{2 π i m τ}`.  The same computation for
`F̃ = Ftgen K̂` gives derivative `0`.

These are the normalisation conditions `value_radialDeriv_F`, `value_radialDeriv_Ftilde`
of `Work.FE.InterpolationSolution` for the constructed pair `(Fgen K, Ftgen K̂)`.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap UpperHalfPlane

noncomputable section

/-- The derivative of the Gaussian factor `gaussTerm τ r = e^{π i τ r²}` in `r`. -/
lemma deriv_gaussTerm (τ : ℍ) (r : ℝ) :
    deriv (fun s : ℝ => Work.Kernels.gaussTerm τ s) r
      = (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (r : ℂ))
        * Work.Kernels.gaussTerm τ r := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (r : ℂ)) r := by
    have h := (hasDerivAt_pow 2 (r : ℂ)).comp r h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun s : ℝ => (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (s : ℂ) ^ 2)
      ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * (2 * (r : ℂ))) r := h2.const_mul _
  have h4 : HasDerivAt
      (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * (s : ℂ) ^ 2))
      (Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * (r : ℂ) ^ 2)
        * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * (2 * (r : ℂ)))) r := by
    simpa only [Function.comp_def] using (Complex.hasDerivAt_exp _).comp r h3
  simp only [Work.Kernels.gaussTerm]
  rw [h4.deriv]
  ring

/-- The value of the Gaussian factor at a sample radius: `e^{π i τ (√(2m))²} = e^{2 π i m τ}`. -/
lemma gaussTerm_rate (τ : ℍ) (m : ℕ) :
    Work.Kernels.gaussTerm τ (rate m) = dirichletTerm m τ := by
  rw [Work.Kernels.gaussTerm, dirichletTerm]
  rw [gauss_exponent_rate τ m]

/-- The kernel term of (5.2), `r ↦ 4 sin²(π r²/2) · I r`, has derivative `0` at a point
where the sine factor vanishes: the prefactor vanishes at second order there. -/
lemma deriv_kernelTerm_eq_zero (I : ℝ → ℂ) (x : ℝ) (hI : DifferentiableAt ℝ I x)
    (hx : Complex.sin (Real.pi * (x : ℂ) ^ 2 / 2) = 0) :
    deriv (fun r : ℝ => 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 * I r) x = 0 := by
  have hS : DifferentiableAt ℝ
      (fun r : ℝ => 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2) x := by
    fun_prop
  have hSd : deriv (fun r : ℝ => 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2) x = 0 := by
    have hV : DifferentiableAt ℝ (fun r : ℝ => Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2)) x := by
      fun_prop
    have key : deriv (fun r : ℝ =>
        4 * ((fun s : ℝ => Complex.sin (Real.pi * (s : ℂ) ^ 2 / 2)) ^ 2) r) x = 0 := by
      rw [deriv_const_mul 4 (hV.pow 2), deriv_pow hV 2]
      simp [hx]
    exact key
  have h0 : deriv
      ((fun r : ℝ => 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2) * I) x = 0 := by
    rw [deriv_mul hS hI, hSd]
    simp [hx]
  exact h0

/-- The derivative of the kernel term of (5.2) at a sample radius vanishes, `K` arbitrary. -/
lemma deriv_kernelTransform_eq_zero (K : ℍ → ℍ → ℂ) (τ : ℍ) (x : ℝ)
    (hK : DifferentiableAt ℝ (fun r : ℝ =>
      ∫ t in Set.Ioi 0, Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) x)
    (hx : Complex.sin (Real.pi * (x : ℂ) ^ 2 / 2) = 0) :
    deriv (fun r : ℝ => Work.Kernels.kernelTransform K τ r) x = 0 :=
  deriv_kernelTerm_eq_zero _ _ hK hx

/-- The derivative of `Ftgen K τ` at a sample radius vanishes, `K` arbitrary. -/
lemma deriv_Ftgen_rate (K : ℍ → ℍ → ℂ) (τ : ℍ) (m : Set.Ici (1 : ℕ))
    (hK : DifferentiableAt ℝ (fun r : ℝ =>
      ∫ t in Set.Ioi 0, Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (rate m.1)) :
    deriv (fun r : ℝ => Work.Kernels.Ftgen K τ r) (rate m.1) = 0 :=
  deriv_kernelTerm_eq_zero _ _ hK (sin_rate_sq_div_two m.1)

/-- The derivative of `Fgen K τ` at a sample radius. -/
lemma deriv_Fgen_rate (K : ℍ → ℍ → ℂ) (τ : ℍ) (m : Set.Ici (1 : ℕ))
    (hK : DifferentiableAt ℝ (fun r : ℝ =>
      ∫ t in Set.Ioi 0, Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (rate m.1)) :
    deriv (fun r : ℝ => Work.Kernels.Fgen K τ r) (rate m.1)
      = (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (rate m.1 : ℂ))
        * dirichletTerm m.1 τ := by
  have hKernel : DifferentiableAt ℝ
      (fun r : ℝ => Work.Kernels.kernelTransform K τ r) (rate m.1) := by
    have hsin : DifferentiableAt ℝ
        (fun r : ℝ => 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2) (rate m.1) := by
      fun_prop
    have h := hsin.mul hK
    exact h
  have hGauss : DifferentiableAt ℝ (fun r : ℝ => Work.Kernels.gaussTerm τ r) (rate m.1) := by
    show DifferentiableAt ℝ
      (fun r : ℝ => Complex.exp (Real.pi * Complex.I * (τ : ℂ) * (r : ℂ) ^ 2)) (rate m.1)
    fun_prop
  have hmain : deriv
      ((fun r : ℝ => Work.Kernels.gaussTerm τ r)
        + (fun r : ℝ => Work.Kernels.kernelTransform K τ r)) (rate m.1)
      = (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (rate m.1 : ℂ))
        * dirichletTerm m.1 τ := by
    rw [deriv_add hGauss hKernel, deriv_gaussTerm, gaussTerm_rate]
    rw [deriv_kernelTransform_eq_zero K τ _ hK (sin_rate_sq_div_two m.1)]
    ring
  exact hmain

theorem KernelSampleDerivValues (K Khat : ℍ → ℍ → ℂ) (τ : ℍ) (m : Set.Ici (1 : ℕ))
    (hK : DifferentiableAt ℝ (fun r : ℝ =>
      ∫ t in Set.Ioi 0, Work.Kernels.Kaxis K τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (rate m.1))
    (hKhat : DifferentiableAt ℝ (fun r : ℝ =>
      ∫ t in Set.Ioi 0, Work.Kernels.Kaxis Khat τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (rate m.1)) :
    deriv (fun r : ℝ => Work.Kernels.Fgen K τ r) (rate m.1)
        = (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (rate m.1 : ℂ)) * dirichletTerm m.1 τ ∧
      deriv (fun r : ℝ => Work.Kernels.Ftgen Khat τ r) (rate m.1) = 0 := by
  exact ⟨deriv_Fgen_rate K τ m hK, deriv_Ftgen_rate Khat τ m hKhat⟩

end

end Work.FunctionalEquations
