import Mathlib
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.FourierExpansion
import Submission.Work.FunctionalEquations.FourierSeriesHelpers
import Submission.Work.FunctionalEquations.SeminormGrowthOfRadialGrowth
import Submission.Work.FunctionalEquations.SeminormFourierGrowth
import Submission.Work.FunctionalEquations.HolomorphicFourierExpansion
import Submission.Work.FunctionalEquations.DecayExpansionDifference
import Submission.Work.FunctionalEquations.FourierExpansionSatisfiesFE
import Submission.Work.FunctionalEquations.FourierDataExtraction

/-!
# The Fourier-transform relations of Section 8 from the uniqueness lemma

Section 8 of CKMRV (*Universal optimality of the E8 and Leech lattices and interpolation
formulas*, Ann. of Math. **196** (2022)) deduces the Fourier-transform relations
`ã_n = â_n`, `b̃_n = b̂_n` of the coefficients of the two generating functions from the
uniqueness lemma `lem:noPsolutions` (`Work.FE.HomogeneousRigidity`).

The argument, formalised here: write `𝓕_x F`, `𝓕_x F̃` for the two Dirichlet series whose
coefficients are the Fourier transforms of the coefficients of `F`, `F̃`
(`Work.FE.fourierExpansionGen`, `Work.FE.fourierExpansionTildeGen`).  By
`Work.FunctionalEquations.FourierExpansionSatisfiesFE` the pair `(𝓕_x F̃, 𝓕_x F)` satisfies
the same three functional equations as `(F, F̃)`, so the difference

`(F - 𝓕_x F̃, F̃ - 𝓕_x F)`

satisfies the *homogeneous* system; it is holomorphic in `τ`
(`Work.FunctionalEquations.HolomorphicFourierExpansion`) and of size
`o(e^{-2π (k₀-1) Im τ})` in the strip (`Work.FunctionalEquations.DecayExpansionDifference`),
so `HomogeneousRigidity n (k₀ - 1)` forces it to vanish.  Hence
`F̃(τ,x) = 𝓕_x F(τ,x)` for all `τ` in the upper half plane, and comparing the two Dirichlet
expansions (`Work.FunctionalEquations.fourierData_of_expansion_eq`) gives the
Kronecker-delta relations for the coefficients.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

theorem Section8FourierDataOfRigidity {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (hR : HomogeneousRigidity n ((k₀ : ℝ) - 1)) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) (hExp : ExpansionDataGen n k₀ S basis) :
    Section8FourierDataGen n k₀ S basis := by
  have hgrow : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ (m : Set.Ici k₀) (j : Fin 4) (x : E n),
        ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N :=
    hExp.2.2.2.2
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
  obtain ⟨hFEt_recur, hFE_recur, hFE_pois⟩ := FourierExpansionSatisfiesFE S basis hExp
  obtain ⟨hdec_F, hdec_Ft⟩ := DecayExpansionDifference hk S basis hExp hbf
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
  have hrig := hR g gt hholo_g hholo_gt hrecur_g hrecur_gt hpois hdec_F hdec_Ft
  -- `F̃` agrees with the crossed Fourier expansion, and the coefficients are read off
  refine fourierData_of_expansion_eq hk S basis hExp hbv hbf ?_
  intro τ x hτ
  have h := (hrig τ x hτ).2
  rw [hgt] at h
  exact sub_eq_zero.mp h

end Work.FunctionalEquations
