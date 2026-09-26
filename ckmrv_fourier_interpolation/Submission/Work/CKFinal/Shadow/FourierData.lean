import Submission.Work.Section8P.FourierData
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Coefficients
import Submission.Work.CKFinal.Shadow.DecayExpansionDifference
import Submission.Work.CKFinal.Shadow.Defs
import Submission.Work.CKFinal.Shadow.DeltaGen
import Submission.Work.CKFinal.Shadow.DifferenceExpansionF
import Submission.Work.CKFinal.Shadow.DifferenceExpansionFtilde
import Submission.Work.CKFinal.Shadow.ExpansionData
import Submission.Work.CKFinal.Shadow.ExpansionDataShiftTwo
import Submission.Work.CKFinal.Shadow.ExpansionDataTwoOfDecay
import Submission.Work.CKFinal.Shadow.ExpansionFromFunctionalEquations
import Submission.Work.CKFinal.Shadow.FourierDataExtraction
import Submission.Work.CKFinal.Shadow.FourierExpansionSatisfiesFE
import Submission.Work.CKFinal.Shadow.FunctionCoefficients
import Submission.Work.CKFinal.Shadow.FunctionDerivExpansion
import Submission.Work.CKFinal.Shadow.FunctionExpansion
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.HasDerivAtParametricIntegral
import Submission.Work.CKFinal.Shadow.InPExpansion
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.MainGen
import Submission.Work.CKFinal.Shadow.ParametricDerivBounds
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionCLMGen
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.ReconstructionGaussianGen
import Submission.Work.CKFinal.Shadow.Reduction
import Submission.Work.CKFinal.Shadow.Section8ValueDataOfRigidity
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms
import Submission.Work.CKFinal.Shadow.TauDiffSetup
import Submission.Work.CKFinal.Shadow.TauDifferenceExpansionF
import Submission.Work.CKFinal.Shadow.TauDifferenceExpansionFtilde
import Submission.Work.CKFinal.Shadow.Thm31Adapter
import Submission.Work.CKFinal.Shadow.ValuePatternGen
import Submission.Work.CKFinal.Shadow.growth_combination
import Submission.Work.CKFinal.Shadow.kernel_isSchwartz
import Submission.Work.CKFinal.Shadow.psi_deriv_bound
import Submission.Work.CKFinal.Shadow.psi_smooth

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (SeminormFourierGrowth)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (norm_apply_le_of_radial)
end Work.FunctionalEquations
namespace Work.Section8P
export _root_.Work.Section8P (InP_fourierExpansionGen)
end Work.Section8P
namespace Work.Section8P
export _root_.Work.Section8P (InP_fourierExpansionTildeGen)
end Work.Section8P
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (HolomorphicFourierExpansion)
end Work.FunctionalEquations

/-
# The Fourier-transform relations of Section 8 from the paper-faithful rigidity lemma

`Submission/Work/FunctionalEquations/Section8FourierDataOfRigidity.lean` derives the
Fourier-transform relations `ã = â`, `b̃ = b̂` of Section 8 of CKMRV from the *`InP`-free*
uniqueness statement `Work.FE.HomogeneousRigidity`, which is false
(`Submission/Work/Rigidity/Counterexample.lean`).  This file redoes the same argument for
the paper-faithful statement `Work.Rigidity.HomogeneousRigidityP`, supplying the two
`𝒫`-membership hypotheses from the expansion data.

The pair `(F - 𝓕_x F̃, F̃ - 𝓕_x F)` is the difference of the generating functions from the
crossed Fourier expansions; each component is a difference of two Dirichlet expansions of
the shape `A + 2πiτ·B` with polynomially bounded coefficients (the coefficients of
`𝓕_x F`, `𝓕_x F̃` are the Fourier transforms of the coefficient families, whose polynomial
growth is `Work.FunctionalEquations.SeminormFourierGrowth` +
`Work.FunctionalEquations.SeminormGrowthOfRadialGrowth`), hence lies in `𝒫`.

## Main result

* `Work.Section8P.Section8FourierDataGen_of_rigidityP` :
  `Work.FE.Section8FourierDataGen n k₀ S basis` from `HomogeneousRigidityP n (k₀ - 1)`.
-/

namespace Work.Section8P

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Work.FunctionalEquations
open Filter Topology
open scoped FourierTransform SchwartzMap UpperHalfPlane

noncomputable section

theorem Section8FourierDataGen_of_rigidityP {n : ℕ} [NeZero n] {k₀ : ℕ} {c : ℝ}
    (hk : 1 ≤ k₀) (hc : (k₀ : ℝ) - 1 = c) (hR : Work.Rigidity.HomogeneousRigidityP n c)
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) :
    Section8FourierDataGen n k₀ S basis := by
  rw [← hc] at hR
  obtain ⟨hFexp, hFtexp, hDFexp, hDFtexp, hGrowExp⟩ := hExp
  have hExpA : ExpansionDataGen n k₀ S basis := ⟨hFexp, hFtexp, hDFexp, hDFtexp, hGrowExp⟩
  have hgrow : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ (m : Set.Ici k₀) (j : Fin 4) (x : E n),
        ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N :=
    hExpA.2.2.2.2
  -- Schwartz-seminorm growth of the basis and of its Fourier transforms
  have hsemi_basis : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (j : Fin 4),
      (SchwartzMap.seminorm ℂ k l) (basis (m, j)).1 ≤ C * ((m.1 : ℝ) + 1) ^ N :=
    SeminormGrowthOfRadialGrowth basis hgrow
  have hsemi_ft : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (j : Fin 4),
      (SchwartzMap.seminorm ℂ k l)
          ((FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, j)).1))
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
    intro k l
    obtain ⟨C0, N0, hC0, h0⟩ :=
      SeminormFourierGrowth (fun m : Set.Ici k₀ => (basis (m, 0)).1) (fun k l => by
        obtain ⟨C, N, hC, h⟩ := hsemi_basis k l
        exact ⟨C, N, hC, fun m => h m 0⟩) k l
    obtain ⟨C1, N1, hC1, h1⟩ :=
      SeminormFourierGrowth (fun m : Set.Ici k₀ => (basis (m, 1)).1) (fun k l => by
        obtain ⟨C, N, hC, h⟩ := hsemi_basis k l
        exact ⟨C, N, hC, fun m => h m 1⟩) k l
    obtain ⟨C2, N2, hC2, h2⟩ :=
      SeminormFourierGrowth (fun m : Set.Ici k₀ => (basis (m, 2)).1) (fun k l => by
        obtain ⟨C, N, hC, h⟩ := hsemi_basis k l
        exact ⟨C, N, hC, fun m => h m 2⟩) k l
    obtain ⟨C3, N3, hC3, h3⟩ :=
      SeminormFourierGrowth (fun m : Set.Ici k₀ => (basis (m, 3)).1) (fun k l => by
        obtain ⟨C, N, hC, h⟩ := hsemi_basis k l
        exact ⟨C, N, hC, fun m => h m 3⟩) k l
    refine ⟨C0 + C1 + C2 + C3, N0 + N1 + N2 + N3, by positivity, ?_⟩
    intro m j
    have hp : (1 : ℝ) ≤ (m.1 : ℝ) + 1 := by
      have h0' : (0 : ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
      linarith
    fin_cases j
    · exact le_trans (h0 m) (mul_le_mul (by linarith) (pow_le_pow_right₀ hp (by omega))
        (by positivity) (by positivity))
    · exact le_trans (h1 m) (mul_le_mul (by linarith) (pow_le_pow_right₀ hp (by omega))
        (by positivity) (by positivity))
    · exact le_trans (h2 m) (mul_le_mul (by linarith) (pow_le_pow_right₀ hp (by omega))
        (by positivity) (by positivity))
    · exact le_trans (h3 m) (mul_le_mul (by linarith) (pow_le_pow_right₀ hp (by omega))
        (by positivity) (by positivity))
  -- pointwise polynomial bounds on the coefficients and their Fourier transforms
  have hbf : ∀ j : Fin 4, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (x : E n),
      ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, j)).1) x‖
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
    intro j
    obtain ⟨C, N, hC, h⟩ := hsemi_ft 0 0
    exact ⟨C, N, hC, fun m x =>
      le_trans (SchwartzMap.norm_le_seminorm ℂ _ x) (h m j)⟩
  have hbv : ∀ j : Fin 4, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (x : E n),
      ‖(basis (m, j)).1 x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N := by
    intro j
    obtain ⟨C, N, hC, h⟩ := hgrow 0 0
    refine ⟨C, N, hC, fun m x => norm_apply_le_of_radial (basis (m, j)).2 (fun y => ?_) x⟩
    have hmy := h m j y
    simpa using hmy
  -- the three functional equations of the crossed Fourier expansion
  obtain ⟨hFEt_recur, hFE_recur, hFE_pois⟩ := FourierExpansionSatisfiesFE S basis hExpA
  obtain ⟨hdec_F, hdec_Ft⟩ := DecayExpansionDifference hk S basis hExpA hbf
  -- the expansions of the two generating functions in the `dirichletExpansion` form
  have hFdir : ∀ (x : E n) (τ : ℂ), 0 < τ.im → S.F τ x = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => (basis (m, 0)).1 x)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 2)).1 x) τ := by
    intro x τ hτ
    rw [hFexp τ x hτ]
    rfl
  have hFtdir : ∀ (x : E n) (τ : ℂ), 0 < τ.im → S.Ftilde τ x = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => (basis (m, 1)).1 x)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 3)).1 x) τ := by
    intro x τ hτ
    rw [hFtexp τ x hτ]
    rfl
  -- the two generating functions lie in `𝒫`
  obtain ⟨Cb0, Nb0, hCb0, hb0⟩ := hbv 0
  obtain ⟨Cb1, Nb1, hCb1, hb1⟩ := hbv 1
  obtain ⟨Cb2, Nb2, hCb2, hb2⟩ := hbv 2
  obtain ⟨Cb3, Nb3, hCb3, hb3⟩ := hbv 3
  have hInP_F : ∀ x : E n, Work.Kernels.InP (fun τ : ℍ => S.F (τ : ℂ) x) := fun x =>
    InP_F_at (k₀ := k₀) (S := S) (basis := basis) (x₀ := x)
      (C₀ := Cb0) (N₀ := Nb0) (C₂ := Cb2) (N₂ := Nb2) hCb0 (fun m => hb0 m x)
      hCb2 (fun m => hb2 m x) (fun τ hτ => hFdir x τ hτ)
  have hInP_Ft : ∀ x : E n, Work.Kernels.InP (fun τ : ℍ => S.Ftilde (τ : ℂ) x) := fun x =>
    InP_Ftilde_at (k₀ := k₀) (S := S) (basis := basis) (x₀ := x)
      (C₁ := Cb1) (N₁ := Nb1) (C₃ := Cb3) (N₃ := Nb3) hCb1 (fun m => hb1 m x)
      hCb3 (fun m => hb3 m x) (fun τ hτ => hFtdir x τ hτ)
  -- the two crossed Fourier expansions lie in `𝒫`
  obtain ⟨Cf0, Nf0, hCf0, hf0⟩ := hbf 0
  obtain ⟨Cf1, Nf1, hCf1, hf1⟩ := hbf 1
  obtain ⟨Cf2, Nf2, hCf2, hf2⟩ := hbf 2
  obtain ⟨Cf3, Nf3, hCf3, hf3⟩ := hbf 3
  have hInP_gen : ∀ x : E n,
      Work.Kernels.InP (fun τ : ℍ => fourierExpansionGen k₀ basis (τ : ℂ) x) :=
    InP_fourierExpansionGen (k₀ := k₀) basis hCf0 (fun m x => hf0 m x)
      hCf2 (fun m x => hf2 m x)
  have hInP_genTilde : ∀ x : E n,
      Work.Kernels.InP (fun τ : ℍ => fourierExpansionTildeGen k₀ basis (τ : ℂ) x) :=
    InP_fourierExpansionTildeGen (k₀ := k₀) basis hCf1 (fun m x => hf1 m x)
      hCf3 (fun m x => hf3 m x)
  -- the difference pair to which the uniqueness lemma is applied
  set g : ℂ → E n → ℂ := fun τ x => S.F τ x - fourierExpansionTildeGen k₀ basis τ x with hg
  set gt : ℂ → E n → ℂ := fun τ x => S.Ftilde τ x - fourierExpansionGen k₀ basis τ x with hgt
  have hholo_g : ∀ x : E n, DifferentiableOn ℂ (fun τ : ℂ => g τ x) {τ : ℂ | 0 < τ.im} := by
    intro x
    have h1 := S.holomorphic_F x
    have h2 := (HolomorphicFourierExpansion hk basis hsemi_ft x).2
    rw [hg]
    exact h1.sub h2
  have hholo_gt : ∀ x : E n, DifferentiableOn ℂ (fun τ : ℂ => gt τ x) {τ : ℂ | 0 < τ.im} := by
    intro x
    have h1 := S.holomorphic_Ftilde x
    have h2 := (HolomorphicFourierExpansion hk basis hsemi_ft x).1
    rw [hgt]
    exact h1.sub h2
  have hrecur_g : ∀ (τ : ℂ) (x : E n), 0 < τ.im → g (τ + 2) x - 2 * g (τ + 1) x + g τ x = 0 := by
    intro τ x hτ
    have h1 := S.recur_F τ x hτ
    have h2 := hFEt_recur τ x hτ
    simp only [hg]
    linear_combination h1 - h2
  have hrecur_gt : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      gt (τ + 2) x - 2 * gt (τ + 1) x + gt τ x = 0 := by
    intro τ x hτ
    have h1 := S.recur_Ftilde τ x hτ
    have h2 := hFE_recur τ x hτ
    simp only [hgt]
    linear_combination h1 - h2
  have hpois : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      g τ x + slashFactor n τ * gt (-1 / τ) x = 0 := by
    intro τ x hτ
    have h1 := S.functional_equation τ x hτ
    have h2 := hFE_pois τ x hτ
    simp only [hg, hgt]
    linear_combination h1 - h2
  have hInPg : ∀ x : E n, Work.Kernels.InP (fun τ : ℍ => g (τ : ℂ) x) := by
    intro x
    simpa only [hg] using (hInP_F x).sub (hInP_genTilde x)
  have hInPgt : ∀ x : E n, Work.Kernels.InP (fun τ : ℍ => gt (τ : ℂ) x) := by
    intro x
    simpa only [hgt] using (hInP_Ft x).sub (hInP_gen x)
  have hrig := hR g gt hInPg hInPgt hrecur_g hrecur_gt hpois hdec_F hdec_Ft
  -- `F̃` agrees with the crossed Fourier expansion, and the coefficients are read off
  refine fourierData_of_expansion_eq hk S basis hExpA hbv hbf ?_
  intro τ x hτ
  have h := (hrig τ x hτ).2
  rw [hgt] at h
  exact sub_eq_zero.mp h
end

end Work.Section8P


end Work.CKFinal.Shadow
