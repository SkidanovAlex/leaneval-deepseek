import Submission.Work.FunctionalEquations.FourierDataExtraction
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms
import Submission.Work.CKFinal.Shadow.ValuePatternGen

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (rate_nonneg)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (rate_le)
end Work.FunctionalEquations
namespace Work.FE
export _root_.Work.FE (fourierExpansionGen)
end Work.FE

/-!
# The Fourier-transform relations `ã = â`, `b̃ = b̂` from the pointwise identity

Section 8 of CKMRV deduces `F̃ = 𝓕_x F` (as functions of `τ` and `x`) from the uniqueness
lemma `lem:noPsolutions`, and reads off the Fourier-transform relations of the coefficient
families from the two Dirichlet expansions.

This file contains the bookkeeping half of that step: if, for some solution `S` of the
functional equations with expansion data `basis` (`Work.FE.ExpansionDataGen`), the pointwise
identity `S.Ftilde τ x = fourierExpansionGen k₀ basis τ x` holds on the upper half plane,
and the coefficients of the four families are polynomially bounded (together with the
Fourier transforms of `basis (·,0)` and `basis (·,2)`), then

`(basis (m,1)).1 = 𝓕 (basis (m,0)).1` and `(basis (m,3)).1 = 𝓕 (basis (m,2)).1`.

The proof is the splitting `A(τ) + τ B(τ)` of a Dirichlet expansion with `A`, `B` periodic
(`Work.FunctionalEquations.periodic_split_UHP`) followed by Fourier orthogonality on a
horizontal line (`Work.FunctionalEquations.coeffs_eq_of_tsum_eq_gen`), and the cancellation
of the common factor `2 π i` resp. of the rate `√(2m) ≠ 0`.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-- The rate-weighted version of a polynomial bound is again a polynomial bound. -/
private lemma rate_mul_poly_bound {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (h : ∀ m : Set.Ici k₀, ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ N' : ℕ, ∀ m : Set.Ici k₀,
      ‖(rate m.1 : ℂ) * c m‖ ≤ C' * ((m.1 : ℝ) + 1) ^ N' := by
  refine ⟨C, hC, N + 1, fun m => ?_⟩
  have hr : ‖(rate m.1 : ℂ)‖ = rate m.1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rate_nonneg m.1)]
  rw [norm_mul, hr]
  calc rate m.1 * ‖c m‖ ≤ ((m.1 : ℝ) + 1) * (C * ((m.1 : ℝ) + 1) ^ N) :=
        mul_le_mul (rate_le m.1) (h m) (norm_nonneg _) (by positivity)
    _ = C * ((m.1 : ℝ) + 1) ^ (N + 1) := by rw [pow_succ]; ring

/-- **The Fourier-transform relations from the pointwise identity `F̃ = 𝓕_x F`.**

Hypotheses: the expansion data of `Work.FE.ExpansionDataGen`, polynomial bounds on the
values of the four coefficient families and on the values of the Fourier transforms of
`basis (·,0)`, `basis (·,2)`, and the pointwise identity
`S.Ftilde τ x = fourierExpansionGen k₀ basis τ x` for `Im τ > 0`. -/
theorem fourierData_of_expansion_eq {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis)
    (hbv : ∀ j : Fin 4, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (x : E n),
        ‖(basis (m, j)).1 x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (hbf : ∀ j : Fin 4, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ (m : Set.Ici k₀) (x : E n),
        ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, j)).1) x‖
          ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (heq : ∀ (τ : ℂ) (x : E n), 0 < τ.im → S.Ftilde τ x = fourierExpansionGen k₀ basis τ x) :
    Section8FourierDataGen n k₀ S basis := by
  obtain ⟨-, hFt, -, -, -⟩ := hExp
  have h2pii : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have key : ∀ x : E n,
      (∀ m : Set.Ici k₀,
          (basis (m, 1)).1 x = (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 0)).1) x) ∧
      (∀ m : Set.Ici k₀,
          (basis (m, 3)).1 x = (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (m, 2)).1) x) := by
    intro x
    obtain ⟨C1, N1, hC1, hbd1⟩ := hbv 1
    obtain ⟨C0, N0, hC0, hbd0⟩ := hbf 0
    obtain ⟨C3, N3, hC3, hbd3⟩ := hbv 3
    obtain ⟨C2, N2, hC2, hbd2⟩ := hbf 2
    set A₁ : ℂ → ℂ := fun τ =>
      ∑' k : Set.Ici k₀, (basis (k, 1)).1 x * dirichletTerm k.1 τ with hA₁
    set A₂ : ℂ → ℂ := fun τ =>
      ∑' k : Set.Ici k₀,
        (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (k, 0)).1) x * dirichletTerm k.1 τ
      with hA₂
    set B₁ : ℂ → ℂ := fun τ => 2 * (Real.pi : ℂ) * Complex.I *
      (∑' k : Set.Ici k₀, (rate k.1 : ℂ) * (basis (k, 3)).1 x * dirichletTerm k.1 τ) with hB₁
    set B₂ : ℂ → ℂ := fun τ => 2 * (Real.pi : ℂ) * Complex.I *
      (∑' k : Set.Ici k₀,
        (rate k.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (k, 2)).1) x
          * dirichletTerm k.1 τ) with hB₂
    have per1 : ∀ τ : ℂ, 0 < τ.im → A₁ (τ + 1) = A₁ τ := by
      intro τ _
      rw [hA₁]
      exact periodic_tsum_gen (fun k : Set.Ici k₀ => (basis (k, 1)).1 x) τ
    have per2 : ∀ τ : ℂ, 0 < τ.im → A₂ (τ + 1) = A₂ τ := by
      intro τ _
      rw [hA₂]
      exact periodic_tsum_gen
        (fun k : Set.Ici k₀ =>
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (k, 0)).1) x) τ
    have per3 : ∀ τ : ℂ, 0 < τ.im → B₁ (τ + 1) = B₁ τ := by
      intro τ _
      simp only [hB₁]
      rw [periodic_tsum_gen
        (fun k : Set.Ici k₀ => (rate k.1 : ℂ) * (basis (k, 3)).1 x) τ]
    have per4 : ∀ τ : ℂ, 0 < τ.im → B₂ (τ + 1) = B₂ τ := by
      intro τ _
      simp only [hB₂]
      rw [periodic_tsum_gen
        (fun k : Set.Ici k₀ =>
          (rate k.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (k, 2)).1) x) τ]
    have hEq : ∀ τ : ℂ, 0 < τ.im → A₁ τ + τ * B₁ τ = A₂ τ + τ * B₂ τ := by
      intro τ hτ
      have e1 : S.Ftilde τ x = A₁ τ + τ * B₁ τ := by
        rw [hFt τ x hτ]
        simp only [hA₁, hB₁]
        ring
      have e2 : fourierExpansionGen k₀ basis τ x = A₂ τ + τ * B₂ τ := by
        simp only [fourierExpansionGen, hA₂, hB₂]
        ring
      rw [← e2, ← e1]
      exact heq τ x hτ
    have hsplit : ∀ τ : ℂ, 0 < τ.im → B₁ τ = B₂ τ ∧ A₁ τ = A₂ τ :=
      periodic_split_UHP per1 per2 per3 per4 hEq
    have hAeq : ∀ τ : ℂ, 0 < τ.im →
        (∑' k : Set.Ici k₀, (basis (k, 1)).1 x * dirichletTerm k.1 τ)
          = ∑' k : Set.Ici k₀,
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (k, 0)).1) x
                * dirichletTerm k.1 τ := by
      intro τ hτ
      simpa only [hA₁, hA₂] using (hsplit τ hτ).2
    have hBeq : ∀ τ : ℂ, 0 < τ.im →
        (∑' k : Set.Ici k₀, (rate k.1 : ℂ) * (basis (k, 3)).1 x * dirichletTerm k.1 τ)
          = ∑' k : Set.Ici k₀,
              (rate k.1 : ℂ)
                * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (k, 2)).1) x
                * dirichletTerm k.1 τ := by
      intro τ hτ
      have h := (hsplit τ hτ).1
      simp only [hB₁, hB₂] at h
      exact mul_left_cancel₀ h2pii h
    refine ⟨?_, ?_⟩
    · intro m
      exact coeffs_eq_of_tsum_eq_gen (c := fun k : Set.Ici k₀ => (basis (k, 1)).1 x)
        (c' := fun k : Set.Ici k₀ =>
          (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (k, 0)).1) x)
        ⟨C1, hC1, N1, fun k => hbd1 k x⟩ ⟨C0, hC0, N0, fun k => hbd0 k x⟩ hAeq m
    · intro m
      have h := coeffs_eq_of_tsum_eq_gen
        (c := fun k : Set.Ici k₀ => (rate k.1 : ℂ) * (basis (k, 3)).1 x)
        (c' := fun k : Set.Ici k₀ =>
          (rate k.1 : ℂ) * (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (basis (k, 2)).1) x)
        (rate_mul_poly_bound hC3 (fun k => hbd3 k x))
        (rate_mul_poly_bound hC2 (fun k => hbd2 k x)) hBeq m
      exact mul_left_cancel₀ (rate_ne_zero_gen hk m) h
  refine ⟨fun m => ?_, fun m => ?_⟩
  · ext x
    exact (key x).1 m
  · ext x
    exact (key x).2 m

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
