import Mathlib
import Submission.Work.Drive.UmlaufSetup
import Submission.Work.Drive.sigma_continuous

namespace Work.Drive

open scoped Manifold ContDiff

/-- The lift of Hopf's secant map to an angle function on the closed triangle.

`Work.Drive.sigma c t₀` is a continuous map from the triangle (convex, hence contractible and
locally path connected; the instances `instContractibleTri`, `instLocallyPathConnectedTri` are
in `Submission.Work.Drive.UmlaufSetup`) to `Circle`, and `Circle.exp : ℝ → Circle` is a covering
map (`Circle.isCoveringMap_exp`), so `IsCoveringMap.existsUnique_continuousMap_lifts` gives a
lift `Θ` with `Circle.exp ∘ Θ = sigma c t₀`.  Prescribe the value `Θ (triBase t₀) = θ t₀`; note
`triBase t₀` is the corner `(t₀, t₀)`, where `sigma` is `tangDir c t₀` (the first two branches of
`sigmaPt` fail), and `Circle.exp (θ t₀) = tangDir c t₀ = sigma c t₀ (triBase t₀)` by `hθ`, which
is exactly the compatibility hypothesis of the lifting theorem.  (Continuity of `sigma` is a
separate lemma `Work.Drive.continuous_sigma`.) -/
theorem exists_angle_tri (c : ℝ → ℝ × ℝ) (hc : Work.Drive.RegCurve c) (t₀ : ℝ) (θ : ℝ → ℝ)
    (hθ : ∀ t, Circle.exp (θ t) = Work.Drive.tangDir c t) :
    ∃ Θ : Work.Drive.tri t₀ → ℝ, Continuous Θ ∧
      (∀ p, Circle.exp (Θ p) = Work.Drive.sigma c t₀ p) ∧
      Θ (Work.Drive.triBase t₀) = θ t₀ := by
  have hcont : Continuous (Work.Drive.sigma c t₀) := sigma_continuous c hc t₀
  have he : Circle.exp (θ t₀) = Work.Drive.sigma c t₀ (Work.Drive.triBase t₀) := by
    rw [hθ t₀]
    simp [Work.Drive.sigma, Work.Drive.sigmaPt, Work.Drive.triBase]
  obtain ⟨F, hF1, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      (⟨Work.Drive.sigma c t₀, hcont⟩ : C(Work.Drive.tri t₀, Circle))
      (Work.Drive.triBase t₀) (θ t₀) he
  exact ⟨fun p => F p, F.continuous, fun p => congr_fun hF1.2 p, hF1.1⟩

end Work.Drive
