import Mathlib
import Submission.Diff.ODE
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! The flow of a time-independent smooth field, obtained from the contract `SmoothFlow`. -/

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem flow_of_field
    (hFlow : Submission.Diff.SmoothFlow I M)
    {V : (x : M) → TangentSpace I x}
    (hV : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I)))) :
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s x, Φ s s x = x) ∧
      (∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x)))) ∧
      (∀ s t u x, Φ t u (Φ s t x) = Φ s u x) := by
  have h2 : ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞ (fun p : ℝ × M => p.2) := contMDiff_snd
  have h3 : ContMDiff (𝓘(ℝ,ℝ).prod I) (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun p : ℝ × M => (⟨p.2, V p.2⟩ : TangentBundle I M)) := hV.comp h2
  obtain ⟨Φ, hsm, hself, hcoc, hderiv⟩ := hFlow (fun _ => V) h3
  exact ⟨Φ, hsm, hself, fun s t x => hderiv s t x, hcoc⟩

end Work.Diff.Dim2
