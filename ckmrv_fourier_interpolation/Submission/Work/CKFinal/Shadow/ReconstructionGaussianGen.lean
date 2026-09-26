import Submission.Work.FunctionalEquations.ReconstructionGaussianGen
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (summable_mul_dirichletTerm_gen)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (summable_rate_mul_dirichletTerm_gen)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (coeffs_gaussian_values_gen)
end Work.FunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-!
# The reconstruction formula for the complex Gaussians, general `k₀`

This is the general-`k₀` counterpart of `Work.FE.ReconstructionGaussian`
(`Submission/Work/FunctionalEquations/ReconstructionGaussian.lean`): the defect
functional of the interpolation formula,
`f ↦ ∑ i, (coeffs f i) * (basis i) x₀ - f x₀`, vanishes on the complex Gaussians
`x ↦ exp (π i τ ‖x‖²)`, now for the data `InterpolationSolutionGen n k₀` whose
Fourier expansions are indexed from `k₀` rather than from `1`.

The only new ingredient is the general-`k₀` summability of the Fourier expansion
terms; the rest of the argument is the same as in the `k₀ = 1` case.
-/

/-! ## Summability of the Fourier expansion terms for general `k₀` -/

/-- A polynomial weight times a geometric sequence with ratio `t ∈ [0,1)` is summable. -/
private lemma summable_nat_add_one_pow_mul_geometric' {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * t ^ n := by
  have htabs : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  have hgeom : Summable fun n : ℕ => (n : ℝ) ^ N * t ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one N htabs
  have hgeom1 : Summable fun n : ℕ => t ^ n := summable_geometric_of_norm_lt_one htabs
  have hmain : Summable fun n : ℕ => (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) :=
    (hgeom.add hgeom1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmain
  have hb : ((n : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) := by
    have hmax : ((n : ℝ) + 1) ≤ 2 * max (n : ℝ) 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]; linarith
      · rw [max_eq_right hh.le]; linarith
    have hstep : ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N :=
      pow_le_pow_left₀ (by positivity) hmax N
    have hmaxN : (max (n : ℝ) 1) ^ N ≤ (n : ℝ) ^ N + 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]
        have : (0 : ℝ) ≤ (n : ℝ) ^ N := by positivity
        linarith
      · rw [max_eq_right hh.le]; simp
    calc ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N := hstep
      _ = (2 : ℝ) ^ N * (max (n : ℝ) 1) ^ N := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) :=
          mul_le_mul_of_nonneg_left hmaxN (by positivity)
  calc ((n : ℝ) + 1) ^ N * t ^ n ≤ ((2 : ℝ) ^ N * ((n : ℝ) ^ N + 1)) * t ^ n :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) := by ring

/-- The norm of a real number seen as a complex number. -/
private lemma norm_ofReal_complex' (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]; ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r]

/-- **Summability of the four Fourier expansion terms, general `k₀`.** -/
private theorem SummableExpansionTermsGen_local {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : InterpolationSolutionGen n k₀) (τ : ℂ) (hτ : 0 < τ.im) (x : E n) :
    Summable (fun m : Set.Ici k₀ => (S.basis (m, 0)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici k₀ => (S.basis (m, 1)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici k₀ =>
      (rate m.1 : ℂ) * (S.basis (m, 2)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici k₀ =>
      (rate m.1 : ℂ) * (S.basis (m, 3)).1 x * dirichletTerm m.1 τ) := by
  obtain ⟨C, N, hC, hbound⟩ := SeminormGrowthOfRadialGrowth S.basis S.growth_radial 0 0
  have hb : ∀ (j : Fin 4) (m : Set.Ici k₀),
      ‖(S.basis (m, j)).1 x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N := fun j m =>
    le_trans (SchwartzMap.norm_le_seminorm ℂ _ x) (hbound m j)
  exact ⟨summable_mul_dirichletTerm_gen hC (fun m => hb 0 m) τ hτ,
    summable_mul_dirichletTerm_gen hC (fun m => hb 1 m) τ hτ,
    summable_rate_mul_dirichletTerm_gen hC (fun m => hb 2 m) τ hτ,
    summable_rate_mul_dirichletTerm_gen hC (fun m => hb 3 m) τ hτ⟩

/-! ## The samples of a Gaussian in Dirichlet form -/

private lemma exp_eq_dirichletTerm_gen (k : ℕ) (τ : ℂ) :
    Complex.exp (2 * ↑Real.pi * Complex.I * τ * (k : ℂ)) = dirichletTerm k τ := by
  rw [dirichletTerm]; congr 1; ring

private lemma exp_neg_div_eq_dirichletTerm_gen (k : ℕ) (τ : ℂ) :
    Complex.exp (-(2 * ↑Real.pi * Complex.I * (k : ℂ)) / τ) = dirichletTerm k (-1 / τ) := by
  rw [dirichletTerm]; congr 1; ring_nf

/-- `τ ↦ -1/τ` preserves the upper half plane. -/
private lemma neg_inv_im_pos_gen {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  rw [Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
  have hns : 0 < Complex.normSq τ := by
    rw [Complex.normSq_pos]; intro h; rw [h] at hτ; simp at hτ
  rw [show -0 * τ.re / Complex.normSq τ - -1 * τ.im / Complex.normSq τ
        = τ.im / Complex.normSq τ by ring]
  positivity

/-! ## The reconstruction formula for the Gaussian, general `k₀` -/

/-- **The sampled series of a Gaussian is summable.** -/
private lemma summable_reconstruction_gaussian_gen {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : InterpolationSolutionGen n k₀) (x₀ : E n) (τ : ℂ) (hτ : 0 < τ.im)
    (G : 𝓢(E n, ℂ)) (hG : ∀ x, G x = Work.Core.gaussianFun n τ x) :
    Summable (fun i : SampleIdx k₀ => coeffs n k₀ G i * (S.basis i).1 x₀) := by
  have hτ' : 0 < (-1 / τ).im := neg_inv_im_pos_gen hτ
  have hE := SummableExpansionTermsGen_local S τ hτ x₀
  have hE' := SummableExpansionTermsGen_local S (-1 / τ) hτ' x₀
  have hB : Summable (fun k : Set.Ici k₀ =>
      (S.basis (k, 1)).1 x₀ * dirichletTerm k.1 (-1 / τ)) := hE'.2.1
  have hC : Summable (fun k : Set.Ici k₀ =>
      (rate k.1 : ℂ) * (S.basis (k, 2)).1 x₀ * dirichletTerm k.1 τ) := hE.2.2.1
  have hD : Summable (fun k : Set.Ici k₀ =>
      (rate k.1 : ℂ) * (S.basis (k, 3)).1 x₀ * dirichletTerm k.1 (-1 / τ)) := hE'.2.2.2
  have hj0 : Summable (fun k : Set.Ici k₀ => coeffs n k₀ G (k, 0) * (S.basis (k, 0)).1 x₀) := by
    refine hE.1.congr (fun k => ?_)
    rw [(coeffs_gaussian_values_gen τ hτ G hG k).1]; ring
  have hj1 : Summable (fun k : Set.Ici k₀ => coeffs n k₀ G (k, 1) * (S.basis (k, 1)).1 x₀) := by
    refine (hB.mul_left (slashFactor n τ)).congr (fun k => ?_)
    rw [(coeffs_gaussian_values_gen τ hτ G hG k).2.1]; ring
  have hj2 : Summable (fun k : Set.Ici k₀ => coeffs n k₀ G (k, 2) * (S.basis (k, 2)).1 x₀) := by
    refine (hC.mul_left (2 * (Real.pi : ℂ) * Complex.I * τ)).congr (fun k => ?_)
    rw [(coeffs_gaussian_values_gen τ hτ G hG k).2.2.1]; ring
  have hj3 : Summable (fun k : Set.Ici k₀ => coeffs n k₀ G (k, 3) * (S.basis (k, 3)).1 x₀) := by
    refine (hD.mul_left (2 * (Real.pi : ℂ) * Complex.I * (-1 / τ) * slashFactor n τ)).congr
      (fun k => ?_)
    rw [(coeffs_gaussian_values_gen τ hτ G hG k).2.2.2]; ring
  rw [← summable_norm_iff]
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  refine ⟨fun k => Summable.of_finite, ?_⟩
  have hsum4 : Summable (fun k : Set.Ici k₀ =>
      ‖coeffs n k₀ G (k, 0) * (S.basis (k, 0)).1 x₀‖
        + ‖coeffs n k₀ G (k, 1) * (S.basis (k, 1)).1 x₀‖
        + ‖coeffs n k₀ G (k, 2) * (S.basis (k, 2)).1 x₀‖
        + ‖coeffs n k₀ G (k, 3) * (S.basis (k, 3)).1 x₀‖) :=
    ((hj0.norm.add hj1.norm).add (hj2.norm.add hj3.norm)).congr (fun k => by ring)
  refine hsum4.congr (fun k => ?_)
  rw [tsum_fintype, Fin.sum_univ_four]

/-- **The reconstruction series of a Gaussian equals the functional equation.** -/
private lemma tsum_reconstruction_gaussian_gen {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : InterpolationSolutionGen n k₀) (x₀ : E n) (τ : ℂ) (hτ : 0 < τ.im)
    (G : 𝓢(E n, ℂ)) (hG : ∀ x, G x = Work.Core.gaussianFun n τ x) :
    (∑' i : SampleIdx k₀, coeffs n k₀ G i * (S.basis i).1 x₀)
      = S.F τ x₀ + slashFactor n τ * S.Ftilde (-1 / τ) x₀ := by
  have hτ' : 0 < (-1 / τ).im := neg_inv_im_pos_gen hτ
  have hE := SummableExpansionTermsGen_local S τ hτ x₀
  have hE' := SummableExpansionTermsGen_local S (-1 / τ) hτ' x₀
  have hsum : Summable (fun i : SampleIdx k₀ => coeffs n k₀ G i * (S.basis i).1 x₀) :=
    summable_reconstruction_gaussian_gen S x₀ τ hτ G hG
  rw [Summable.tsum_prod hsum]
  have hpoint : ∀ k : Set.Ici k₀,
      (∑' j : Fin 4, coeffs n k₀ G (k, j) * (S.basis (k, j)).1 x₀)
      = (S.basis (k, 0)).1 x₀ * dirichletTerm k.1 τ
        + (slashFactor n τ * ((S.basis (k, 1)).1 x₀ * dirichletTerm k.1 (-1 / τ))
           + ((2 * (Real.pi : ℂ) * Complex.I * τ)
                * ((rate k.1 : ℂ) * (S.basis (k, 2)).1 x₀ * dirichletTerm k.1 τ)
              + (slashFactor n τ * (2 * (Real.pi : ℂ) * Complex.I * (-1 / τ)))
                * ((rate k.1 : ℂ) * (S.basis (k, 3)).1 x₀ * dirichletTerm k.1 (-1 / τ)))) := by
    intro k
    rw [tsum_fintype, Fin.sum_univ_four]
    obtain ⟨h0, h1, h2, h3⟩ := coeffs_gaussian_values_gen τ hτ G hG k
    rw [h0, h1, h2, h3]; ring
  rw [tsum_congr hpoint]
  have hA : Summable (fun k : Set.Ici k₀ =>
      (S.basis (k, 0)).1 x₀ * dirichletTerm k.1 τ) := hE.1
  have hB : Summable (fun k : Set.Ici k₀ =>
      (S.basis (k, 1)).1 x₀ * dirichletTerm k.1 (-1 / τ)) := hE'.2.1
  have hC : Summable (fun k : Set.Ici k₀ =>
      (rate k.1 : ℂ) * (S.basis (k, 2)).1 x₀ * dirichletTerm k.1 τ) := hE.2.2.1
  have hD : Summable (fun k : Set.Ici k₀ =>
      (rate k.1 : ℂ) * (S.basis (k, 3)).1 x₀ * dirichletTerm k.1 (-1 / τ)) := hE'.2.2.2
  have hslB : Summable (fun k : Set.Ici k₀ =>
      slashFactor n τ * ((S.basis (k, 1)).1 x₀ * dirichletTerm k.1 (-1 / τ))) :=
    hB.mul_left _
  have hc1C : Summable (fun k : Set.Ici k₀ =>
      (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ((rate k.1 : ℂ) * (S.basis (k, 2)).1 x₀ * dirichletTerm k.1 τ)) := hC.mul_left _
  have hc2D : Summable (fun k : Set.Ici k₀ =>
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

theorem ReconstructionGaussianGen {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : InterpolationSolutionGen n k₀) (x₀ : E n)
    (τ : ℂ) (hτ : 0 < τ.im) (G : 𝓢(E n, ℂ))
    (hG : ∀ x, G x = Work.Core.gaussianFun n τ x) :
    (∑' i : SampleIdx k₀, coeffs n k₀ G i * (S.basis i).1 x₀) - G x₀ = 0 := by
  rw [tsum_reconstruction_gaussian_gen S x₀ τ hτ G hG, S.functional_equation τ x₀ hτ, hG x₀]
  ring

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
