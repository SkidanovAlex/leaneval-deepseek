import Mathlib
import Submission.Work.KMTAreas.A7Hi2.cutLevel
import Submission.Work.KMTAreas.A7Hi2.supDeepAux

namespace Work.KMTAreas.A7Hi2

theorem supDeepLe (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          ⨆ (n : ℕ) (_ : Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≤ m₀ + n),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
  supDeepLe_aux ρ hρ hρ1 p hp hptop

end Work.KMTAreas.A7Hi2
