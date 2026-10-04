import Mathlib
import Submission.Work.Diff.STE.ChartComp
import Submission.Work.Diff.STE.contDiffOn_chartComp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE

theorem contDiffOn_locComp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {ι₀ : Type*} (θ : SmoothPartitionOfUnity ι₀ I M) (x₀ : ι₀ → M)
    (g : Submission.Diff.SMet I M) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.locComp θ x₀ g i a b)
      (extChartAt I (x₀ i)).target := by
  -- The two factors are (`unfold`ed) `θ i ∘ (extChartAt I x₀).symm` and `chartComp g (x₀ i) a b`.
  have hθ : ContMDiffOn I 𝓘(ℝ) ∞ (fun q : M => θ i q) Set.univ :=
    ((θ i : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯).contMDiff).contMDiffOn
  have hs : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I (x₀ i)).symm
      (extChartAt I (x₀ i)).target :=
    contMDiffOn_extChartAt_symm (I := I) (x₀ i) (n := ∞)
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E => θ i ((extChartAt I (x₀ i)).symm y)) (extChartAt I (x₀ i)).target :=
    hθ.comp hs (fun y _ => trivial)
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => θ i ((extChartAt I (x₀ i)).symm y)) (extChartAt I (x₀ i)).target :=
    hcomp.contDiffOn
  have h2 := contDiffOn_chartComp (I := I) g (x₀ i) a b
  exact h1.mul h2

end Work.Diff.STE
