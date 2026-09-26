/-
# The `τ`-slashed CKMRV kernels: definitions and the slash law of the transform

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, *Universal optimality of the `E₈` and
Leech lattices and interpolation formulas*, Ann. of Math. 196 (2022)) prove the moderate growth
of the `r`-seminorms of `F₂` on the fundamental domain `𝒟` of `Γ(2)` by a contour shift
(their §5.2, in particular equation (contourshift4)).  The four cusps `-1, 0, 1, ∞` of `𝒟` are
handled by the four pairs `(F, I)`, `(-F̃, S)`, `(F₂|_{d/2}TS, TS)`, `(F₂|_{d/2}T⁻¹S, T⁻¹S)`;
in each case the contour integral to be estimated is that of the *`τ`-slashed* kernel

  `(K^{(d)}|^τ_{d/2}γ)(τ,z) = j(γ,τ)^{-d/2} K^{(d)}(γ·τ, z)`,

with `γ ∈ {I, S, TS, T⁻¹S}`, and the pointwise estimates used are the uniform-in-`γ` quotient
bounds of CKMRV Lemma 4.12, `(quotientbounds1new)` and `(quotientbounds2new)`.

This file contains the interface of that analytic core: the definition of the slashed kernel
`Work.Asymptotics.slashKernel`, the elementary fact that the transform of a slashed kernel is the
automorphy factor times the transform at the slashed point
(`Work.Asymptotics.kernelTransform_slashKernel`), and the target statement
(`Work.Asymptotics.funnel_seminorm_slashed`) asserting the moderate growth of the `r`-seminorms of
the transform of the slashed kernel on the funnel

  `𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}`,

for the four group elements above.  Instantiated at `γ = I` it is (up to the trivial factor
`j(I,τ) = 1`) the statement `Work.Asymptotics.kernelTransform_seminorm_funnel`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels


noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The `τ`-slash of the CKMRV kernel `K^{(d)}` at weight `d/2`, as a kernel in the two
variables `(τ, z)`:

  `slashKernel ℓ d γ τ z = (K^{(d)}(·,z) ∣[d/2] γ) τ = j(γ,τ)^{-d/2} K^{(d)}(γ·τ, z)`. -/
def slashKernel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (γ : SL(2,ℤ)) : ℍ → ℍ → ℂ :=
  fun τ z => SlashAction.map ((d : ℤ) / 2) γ (fun σ : ℍ => Work.Kernels.Kfun ℓ d σ z) τ

lemma slashKernel_apply (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (γ : SL(2,ℤ)) (z τ : ℍ) :
    slashKernel ℓ d γ τ z
      = Work.Kernels.Kfun ℓ d (γ • τ) z * (Work.Kernels.jFun γ (τ : ℂ)) ^ (-((d : ℤ) / 2)) :=
  Work.Kernels.slash_apply' _ _ γ τ

/-- **The transform of a slashed kernel.**  Since `kernelTransform` is complex-linear in the
kernel and the second variable is untouched by the `τ`-slash, the transform of the slashed kernel
at `τ` is the automorphy factor `j(γ,τ)^{-d/2}` times the transform of `K` at the slashed point
`γ·τ`. -/
lemma kernelTransform_slashKernel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (γ : SL(2,ℤ))
    (τ : UpperHalfPlane) (r : ℝ) :
    Work.Kernels.kernelTransform (slashKernel ℓ d γ) τ r
      = (Work.Kernels.jFun γ (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (γ • τ) r := by
  have hKaxis : ∀ t : ℝ, Work.Kernels.Kaxis (slashKernel ℓ d γ) τ t
      = (Work.Kernels.jFun γ (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (γ • τ) t := by
    intro t
    rw [Work.Kernels.Kaxis, Work.Kernels.Kaxis]
    by_cases h : 0 < t
    · simp only [dif_pos h]
      rw [slashKernel_apply ℓ d γ _ τ]
      ring
    · simp only [dif_neg h]
      ring
  have hInt : (∫ t in Set.Ioi 0,
        Work.Kernels.Kaxis (slashKernel ℓ d γ) τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = (Work.Kernels.jFun γ (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
        ∫ t in Set.Ioi 0, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (γ • τ) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    have : (fun t => Work.Kernels.Kaxis (slashKernel ℓ d γ) τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        = fun t => (Work.Kernels.jFun γ (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
            (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (γ • τ) t
              * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
      funext t; rw [hKaxis t]; ring
    rw [this]
    exact MeasureTheory.integral_const_mul _ _
  unfold Work.Kernels.kernelTransform
  rw [hInt]
  ring


end Work.Asymptotics
