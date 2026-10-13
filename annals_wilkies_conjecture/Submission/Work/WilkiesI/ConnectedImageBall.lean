import Mathlib
import Submission.Work.Wilkies.Defs

namespace Work.WilkiesI

theorem ConnectedImageBall {μ n : ℕ} {U : Set (Fin μ → ℝ)} {ψ : (Fin μ → ℝ) → (Fin n → ℝ)} (hψ : ContinuousOn ψ U) {t₀ : Fin μ → ℝ} {η : ℝ} (hη : 0 < η) (hball : Metric.ball t₀ η ⊆ U) : IsConnected (ψ '' Metric.ball t₀ η) :=
  (Metric.isConnected_ball hη).image ψ (hψ.mono hball)

end Work.WilkiesI
