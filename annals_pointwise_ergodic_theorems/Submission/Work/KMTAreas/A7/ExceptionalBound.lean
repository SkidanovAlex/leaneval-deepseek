import Mathlib
import Submission.Work.KMTAreas.A7.ExceptionalSupport
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform
import Submission.Work.KMTAreas.A7.KmtProjUniform
import Submission.Work.KMTAreas.A7.ExcAux2

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract
open Work.Analysis.EndVar

theorem ExceptionalBound (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r → ∃ K : NNReal → NNReal,
      ∀ (ρ : ℝ) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        0 < ρ → ρ ≤ 1 → 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7.exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  -- the two ingredients: the `ρ`-uniform projection bound and the parameter bound
  have hProj : ∀ (qR : ℝ), 1 < qR → ∃ C : ℕ → ℤ → NNReal, (∀ l k, 0 < C l k) ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (l : ℕ) (k : ℤ) (u : ℤ → ℂ),
        eLpNorm (kmtProj ρ l k u) (ENNReal.ofReal qR) Measure.count
          ≤ ENNReal.ofReal (C l k : ℝ) * eLpNorm u (ENNReal.ofReal qR) Measure.count := by
    intro qR hqR
    obtain ⟨R, hRpos, hR⟩ := KmtKernelL1Uniform
    obtain ⟨C, hCpos, hC⟩ := KmtProjUniform hqR hRpos hR
    exact ⟨C, hCpos, hC⟩
  have hSupp : SuppBound excBnd := by
    refine ⟨fun C₀ => ?_, ?_⟩
    · unfold excBnd
      have : (0:ℕ) < 8 * (C₀ + 2) ^ 2 + 64 := by positivity
      omega
    · intro C₀ ρ l₁ l₂ k₁ k₂ N hC₀ hρ0 hρ1 hl₁ hl₂ hk₁ hk₂ hmain hsplit
      exact ExceptionalSupport C₀ ρ l₁ l₂ k₁ k₂ N hC₀ hρ0 hρ1 hl₁ hl₂ hk₁ hk₂ hmain hsplit
  exact ExceptionalBound_of_ingredients hProj hSupp P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum

end Work.KMTAreas.A7
