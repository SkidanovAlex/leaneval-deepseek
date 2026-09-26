import Submission.Work.FunctionalEquations.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (neg_inv_im_pos)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (coeffs_gaussian_values)
end Work.FunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-!
# The reconstruction formula for the complex Gaussians (CKMRV, Step 3 of Theorem 3.1)

The defect functional of the interpolation formula,
`f ↦ ∑ i, (coeffs f i) * (basis i) x₀ - f x₀`, vanishes on the complex Gaussians
`x ↦ exp (π i τ ‖x‖²)`.  This is the base case of the density argument of Step 3 of the
proof of CKMRV Theorem 3.1: the four sampled coefficients of a Gaussian are explicit
(`coeffs_gaussian_values`), the sum over the sample index reorganises into the sums
appearing in the two Fourier expansions of `F` and `F̃`, and the functional equation
`F τ x + (i/τ)^{n/2} F̃ (-1/τ) x = exp (π i τ ‖x‖²)` gives the value.

The lemma `ReconstructionGaussian` proved at the end of this file is exactly this
statement; `Work.FE.interpolationBasis_of_functionalEquations` uses it together with
`ReconstructionCLM` and `DensityOfGaussians` to obtain the interpolation formula for
all radial Schwartz functions.
-/

/-! ## Elementary rewritings of the exponential and the Gaussian samples -/

private lemma exp_eq_dirichletTerm (k : ℕ) (τ : ℂ) :
    Complex.exp (2 * ↑Real.pi * Complex.I * τ * (k : ℂ)) = dirichletTerm k τ := by
  rw [dirichletTerm]; congr 1; ring

private lemma exp_neg_div_eq_dirichletTerm (k : ℕ) (τ : ℂ) :
    Complex.exp (-(2 * ↑Real.pi * Complex.I * (k : ℂ)) / τ) = dirichletTerm k (-1 / τ) := by
  rw [dirichletTerm]; congr 1; ring_nf

/-! ## The reconstruction formula for the Gaussian -/

/-- **The sampled series of a Gaussian is summable.**  Since `Fin 4` is finite, it is
enough that the four `j`-components are summable; each is one of the four Dirichlet
series of `SummableExpansionTerms`, at `τ` for `j = 0, 2` and at `-1/τ` for `j = 1, 3`,
multiplied by the explicit Gaussian factors. -/
private lemma summable_reconstruction_gaussian {n : ℕ} [NeZero n]
    (S : InterpolationSolution n) (x₀ : E n) (τ : ℂ) (hτ : 0 < τ.im)
    (G : 𝓢(E n, ℂ)) (hG : ∀ x, G x = Work.Core.gaussianFun n τ x) :
    Summable (fun i : SampleIdx 1 => coeffs n 1 G i * (S.basis i).1 x₀) := by
  have hτ' : 0 < (-1 / τ).im := neg_inv_im_pos hτ
  have hE := SummableExpansionTerms S τ hτ x₀
  have hE' := SummableExpansionTerms S (-1 / τ) hτ' x₀
  have hB : Summable (fun k : Set.Ici 1 =>
      (S.basis (k, 1)).1 x₀ * dirichletTerm k.1 (-1 / τ)) := hE'.2.1
  have hC : Summable (fun k : Set.Ici 1 =>
      (rate k.1 : ℂ) * (S.basis (k, 2)).1 x₀ * dirichletTerm k.1 τ) := hE.2.2.1
  have hD : Summable (fun k : Set.Ici 1 =>
      (rate k.1 : ℂ) * (S.basis (k, 3)).1 x₀ * dirichletTerm k.1 (-1 / τ)) := hE'.2.2.2
  have hj0 : Summable (fun k : Set.Ici 1 => coeffs n 1 G (k, 0) * (S.basis (k, 0)).1 x₀) := by
    refine hE.1.congr (fun k => ?_)
    rw [(coeffs_gaussian_values τ hτ G hG k).1]; ring
  have hj1 : Summable (fun k : Set.Ici 1 => coeffs n 1 G (k, 1) * (S.basis (k, 1)).1 x₀) := by
    refine (hB.mul_left (slashFactor n τ)).congr (fun k => ?_)
    rw [(coeffs_gaussian_values τ hτ G hG k).2.1]; ring
  have hj2 : Summable (fun k : Set.Ici 1 => coeffs n 1 G (k, 2) * (S.basis (k, 2)).1 x₀) := by
    refine (hC.mul_left (2 * (Real.pi : ℂ) * Complex.I * τ)).congr (fun k => ?_)
    rw [(coeffs_gaussian_values τ hτ G hG k).2.2.1]; ring
  have hj3 : Summable (fun k : Set.Ici 1 => coeffs n 1 G (k, 3) * (S.basis (k, 3)).1 x₀) := by
    refine (hD.mul_left (2 * (Real.pi : ℂ) * Complex.I * (-1 / τ) * slashFactor n τ)).congr
      (fun k => ?_)
    rw [(coeffs_gaussian_values τ hτ G hG k).2.2.2]; ring
  rw [← summable_norm_iff]
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  refine ⟨fun k => Summable.of_finite, ?_⟩
  have hsum4 : Summable (fun k : Set.Ici 1 =>
      ‖coeffs n 1 G (k, 0) * (S.basis (k, 0)).1 x₀‖
        + ‖coeffs n 1 G (k, 1) * (S.basis (k, 1)).1 x₀‖
        + ‖coeffs n 1 G (k, 2) * (S.basis (k, 2)).1 x₀‖
        + ‖coeffs n 1 G (k, 3) * (S.basis (k, 3)).1 x₀‖) :=
    ((hj0.norm.add hj1.norm).add (hj2.norm.add hj3.norm)).congr (fun k => by ring)
  refine hsum4.congr (fun k => ?_)
  rw [tsum_fintype, Fin.sum_univ_four]

/-- **The reconstruction series of a Gaussian equals the functional equation.**
The sample sum of the complex Gaussian, reorganised with `Summable.tsum_prod`, is
exactly `F τ x₀ + (i/τ)^{n/2} F̃ (-1/τ) x₀`: the four components `j = 0,1,2,3` of
`coeffs` are the Dirichlet monomials `e^{2π i m τ}`, `(i/τ)^{n/2} e^{-2π i m/τ}`,
`2π i τ √(2m) e^{2π i m τ}` and `2π i (i/τ)^{n/2} √(2m) (-1/τ) e^{-2π i m/τ}`, which is
the value of the two Fourier expansions of `F` and `F̃` at the sample point. -/
private lemma tsum_reconstruction_gaussian {n : ℕ} [NeZero n]
    (S : InterpolationSolution n) (x₀ : E n) (τ : ℂ) (hτ : 0 < τ.im)
    (G : 𝓢(E n, ℂ)) (hG : ∀ x, G x = Work.Core.gaussianFun n τ x) :
    (∑' i : SampleIdx 1, coeffs n 1 G i * (S.basis i).1 x₀)
      = S.F τ x₀ + slashFactor n τ * S.Ftilde (-1 / τ) x₀ := by
  have hτ' : 0 < (-1 / τ).im := neg_inv_im_pos hτ
  have hE := SummableExpansionTerms S τ hτ x₀
  have hE' := SummableExpansionTerms S (-1 / τ) hτ' x₀
  have hsum : Summable (fun i : SampleIdx 1 => coeffs n 1 G i * (S.basis i).1 x₀) :=
    summable_reconstruction_gaussian S x₀ τ hτ G hG
  rw [Summable.tsum_prod hsum]
  have hpoint : ∀ k : Set.Ici 1,
      (∑' j : Fin 4, coeffs n 1 G (k, j) * (S.basis (k, j)).1 x₀)
      = (S.basis (k, 0)).1 x₀ * dirichletTerm k.1 τ
        + (slashFactor n τ * ((S.basis (k, 1)).1 x₀ * dirichletTerm k.1 (-1 / τ))
           + ((2 * (Real.pi : ℂ) * Complex.I * τ)
                * ((rate k.1 : ℂ) * (S.basis (k, 2)).1 x₀ * dirichletTerm k.1 τ)
              + (slashFactor n τ * (2 * (Real.pi : ℂ) * Complex.I * (-1 / τ)))
                * ((rate k.1 : ℂ) * (S.basis (k, 3)).1 x₀ * dirichletTerm k.1 (-1 / τ)))) := by
    intro k
    rw [tsum_fintype, Fin.sum_univ_four]
    obtain ⟨h0, h1, h2, h3⟩ := coeffs_gaussian_values τ hτ G hG k
    rw [h0, h1, h2, h3]; ring
  rw [tsum_congr hpoint]
  have hA : Summable (fun k : Set.Ici 1 =>
      (S.basis (k, 0)).1 x₀ * dirichletTerm k.1 τ) := hE.1
  have hB : Summable (fun k : Set.Ici 1 =>
      (S.basis (k, 1)).1 x₀ * dirichletTerm k.1 (-1 / τ)) := hE'.2.1
  have hC : Summable (fun k : Set.Ici 1 =>
      (rate k.1 : ℂ) * (S.basis (k, 2)).1 x₀ * dirichletTerm k.1 τ) := hE.2.2.1
  have hD : Summable (fun k : Set.Ici 1 =>
      (rate k.1 : ℂ) * (S.basis (k, 3)).1 x₀ * dirichletTerm k.1 (-1 / τ)) := hE'.2.2.2
  have hslB : Summable (fun k : Set.Ici 1 =>
      slashFactor n τ * ((S.basis (k, 1)).1 x₀ * dirichletTerm k.1 (-1 / τ))) :=
    hB.mul_left _
  have hc1C : Summable (fun k : Set.Ici 1 =>
      (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ((rate k.1 : ℂ) * (S.basis (k, 2)).1 x₀ * dirichletTerm k.1 τ)) := hC.mul_left _
  have hc2D : Summable (fun k : Set.Ici 1 =>
      (slashFactor n τ * (2 * (Real.pi : ℂ) * Complex.I * (-1 / τ)))
        * ((rate k.1 : ℂ) * (S.basis (k, 3)).1 x₀ * dirichletTerm k.1 (-1 / τ))) :=
    hD.mul_left _
  rw [Summable.tsum_add hA (hslB.add (hc1C.add hc2D))]
  rw [Summable.tsum_add hslB (hc1C.add hc2D)]
  rw [Summable.tsum_add hc1C hc2D]
  rw [Summable.tsum_mul_left (slashFactor n τ) hB]
  rw [Summable.tsum_mul_left (2 * (Real.pi : ℂ) * Complex.I * τ) hC]
  rw [Summable.tsum_mul_left (slashFactor n τ * (2 * (Real.pi : ℂ) * Complex.I * (-1 / τ))) hD]
  rw [S.expansion_F τ x₀ hτ, S.expansion_Ftilde (-1 / τ) x₀ hτ']
  ring

theorem ReconstructionGaussian {n : ℕ} [NeZero n] (S : InterpolationSolution n) (x₀ : E n)
    (τ : ℂ) (hτ : 0 < τ.im) (G : 𝓢(E n, ℂ))
    (hG : ∀ x, G x = Work.Core.gaussianFun n τ x) :
    (∑' i : SampleIdx 1, coeffs n 1 G i * (S.basis i).1 x₀) - G x₀ = 0 := by
  rw [tsum_reconstruction_gaussian S x₀ τ hτ G hG, S.functional_equation τ x₀ hτ, hG x₀]
  ring

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
