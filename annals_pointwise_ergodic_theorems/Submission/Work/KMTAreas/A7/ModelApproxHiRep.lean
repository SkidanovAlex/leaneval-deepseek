import Mathlib
import Submission.Work.KMTAreas.A7.RepMain

namespace Work.KMTAreas.A7

theorem ModelApproxHiRep (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            1 ≤ l₁ → 1 ≤ l₂ →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
  Work.KMTAreas.A7.repMain P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum

end Work.KMTAreas.A7
