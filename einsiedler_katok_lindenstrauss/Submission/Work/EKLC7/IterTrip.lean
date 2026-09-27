import Mathlib
import Submission.Work.EKLC7.CoordTripDefs
import Submission.Work.EKLC7.TripFubini

namespace Work.EKLC7

theorem IterTrip {e₁ e₂ e₃ : ℝ → Work.EKLContract.SL3} (hc₁ : Continuous e₁) (hc₂ : Continuous e₂) (hc₃ : Continuous e₃) {ψ : ℝ × ℝ × ℝ → Work.EKLContract.SL3} (hψ : Continuous ψ) (hψeq : ∀ x, e₁ x.1 * e₂ x.2.1 * e₃ x.2.2 = ψ x) (hlex : ∀ M : ℝ, ∃ M' : ℝ, ∀ x, (∀ a b : Fin 3, |Work.EKLContract.toMat (ψ x) a b| ≤ M) → |x.1| ≤ M' ∧ |x.2.1| ≤ M' ∧ |x.2.2| ≤ M') {α₁ α₂ α₃ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasureOnCompacts α₁] [MeasureTheory.IsFiniteMeasureOnCompacts α₂] [MeasureTheory.IsFiniteMeasureOnCompacts α₃] {μ₁ μ₂ μ₃ : MeasureTheory.Measure Work.EKLContract.SL3} [MeasureTheory.IsFiniteMeasureOnCompacts μ₁] [MeasureTheory.IsFiniteMeasureOnCompacts μ₂] [MeasureTheory.IsFiniteMeasureOnCompacts μ₃] (h₁ : μ₁ = α₁.map e₁) (h₂ : μ₂ = α₂.map e₂) (h₃ : μ₃ = α₃.map e₃) (f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) : ∫ x, ∫ y, ∫ z, f (x * y * z) ∂μ₃ ∂μ₂ ∂μ₁ = ∫ g, f g ∂((μ₁.prod (μ₂.prod μ₃)).map (fun u : Work.EKLContract.SL3 × Work.EKLContract.SL3 × Work.EKLContract.SL3 => u.1 * u.2.1 * u.2.2)) := by
  rw [h₁, h₂, h₃]
  rw [tripFubini_lhs hc₁ hc₂ hc₃ hψ hψeq hlex f]
  exact (tripFubini_rhs hc₁ hc₂ hc₃ hψeq f).symm

end Work.EKLC7
