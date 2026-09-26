import Mathlib
import Submission.Work.Kernels.Theorem31
import Submission.Work.Residues.ResidueTheoremK

namespace Work.Residues

open MeasureTheory UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold

open Work.Kernels

/-- The group-algebra action `slash k x` unfolded as a finite sum over the support of `x`:
for every function `F : ℍ → ℂ` and every `τ ∈ ℍ`,
`(F ∣[k] x) τ = ∑_{γ ∈ supp x} x_γ · F(γ • τ) · j(γ,τ)^{-k}`. -/
lemma slash_apply_sum (k : ℤ) (x : R) (F : ℍ → ℂ) (τ : ℍ) :
    slash k x F τ
      = ∑ γ ∈ x.coeff.support, x.coeff γ * (F (γ • τ) * (jFun γ (τ : ℂ)) ^ (-k)) := by
  simp only [slash, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  rw [slash_apply']

/-- **The group-algebra action commutes with the contour integral.**  For any function
`f : ℍ → ℝ → ℂ` and any `c : ℝ → ℂ`, if for every `γ` in the support of `x` the function
`t ↦ f (γ • τ) t * c t` is integrable on `(0,∞)`, then the slash of the integral
`σ ↦ ∫_0^∞ f σ t * c t dt` is the integral of the slashed integrand.

This is the algebraic/integral heart of the statement `slash_kernelTransform`: it says that
the finite linear combination of slash operators encoded by `x` may be moved inside the
contour integral, the finite sum being interchanged with the (Bochner) integral by
`MeasureTheory.integral_finsetSum`. -/
lemma slash_integral_mul (k : ℤ) (x : R) (f : ℍ → ℝ → ℂ) (c : ℝ → ℂ) (τ : ℍ)
    (hint : ∀ γ ∈ x.coeff.support,
      IntegrableOn (fun t : ℝ => f (γ • τ) t * c t) (Set.Ioi 0)) :
    slash k x (fun σ : ℍ => ∫ t in Set.Ioi 0, f σ t * c t) τ
      = ∫ t in Set.Ioi 0, slash k x (fun σ : ℍ => f σ t) τ * c t := by
  have hstep : slash k x (fun σ : ℍ => ∫ t in Set.Ioi 0, f σ t * c t) τ
      = ∑ γ ∈ x.coeff.support, ∫ t in Set.Ioi 0,
          (x.coeff γ * (jFun γ (τ : ℂ)) ^ (-k)) * (f (γ • τ) t * c t) := by
    rw [slash_apply_sum]
    refine Finset.sum_congr rfl (fun γ hγ => ?_)
    rw [show x.coeff γ * ((∫ t in Set.Ioi 0, f (γ • τ) t * c t) * (jFun γ (τ:ℂ))^(-k))
        = (x.coeff γ * (jFun γ (τ:ℂ))^(-k)) * (∫ t in Set.Ioi 0, f (γ•τ) t * c t) by ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hstep]
  rw [show (∑ γ ∈ x.coeff.support, ∫ t in Set.Ioi 0,
        (x.coeff γ * (jFun γ (τ : ℂ)) ^ (-k)) * (f (γ • τ) t * c t))
      = ∫ t in Set.Ioi 0, ∑ γ ∈ x.coeff.support,
        (x.coeff γ * (jFun γ (τ : ℂ)) ^ (-k)) * (f (γ • τ) t * c t)
      from (MeasureTheory.integral_finsetSum _ (fun γ hγ => (hint γ hγ).const_mul _)).symm]
  congr 1 with t
  rw [slash_apply_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun γ hγ => ?_)
  ring

/-- **The group-algebra action commutes with the contour integral.**  For a kernel `K`, any
`x ∈ R` and real `r`, the slash of the kernel transform is the integral of the slashed
integrand.  This is the algebraic/integral step in the proof of the second recurrence of
CKMRV Proposition 5.1 (`h5b`): combined with the pointwise kernel identity
`K(·,it)|^τ_{d/2}(S(T-I)²) = 0` (`Work.Residues.Kaxis_Kfun_slash_S_T2`) it shows that the
slashed kernel transform vanishes. -/
theorem slash_kernelTransform (k : ℤ) (x : Work.Kernels.R) (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℍ)
    (hint : ∀ γ ∈ x.coeff.support,
      IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis K (γ • τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    Work.Kernels.slash k x (fun σ : ℍ => Work.Kernels.kernelTransform K σ r) τ
      = 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 *
        ∫ t in Set.Ioi 0, Work.Kernels.slash k x (fun σ : ℍ => Work.Kernels.Kaxis K σ t) τ *
          Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  have h1 : (fun σ : ℍ => Work.Kernels.kernelTransform K σ r)
      = (4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2) •
          (fun σ : ℍ => ∫ t in Set.Ioi 0, Work.Kernels.Kaxis K σ t *
            Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    funext σ
    simp only [Work.Kernels.kernelTransform, Pi.smul_apply, smul_eq_mul]
  rw [h1, Work.Kernels.slash_smul_F]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [slash_integral_mul k x (fun σ t => Work.Kernels.Kaxis K σ t)
        (fun t : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) τ hint]

end Work.Residues
