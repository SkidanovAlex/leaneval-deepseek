import Submission.Work.Morse.flow_box_local
import Submission.Work.Morse.contDiffAt_chartVF
import Submission.Work.Morse.isMIntegralCurveOn_chartVF

set_option synthInstance.maxHeartbeats 400000

/-!
# Local flow boxes

Combines `flow_box_local_aux` with the two chart ingredients: the chart expression of a smooth
vector field is `C¹` at the base point (`contDiffAt_chartVF`) and solutions of the chart equation
are integral curves of the vector field (`isMIntegralCurveOn_chartVF`).
-/

open scoped Manifold ContDiff Topology
open Set Function Metric

namespace Work.Morse

/-- **Local flow box.** Every point of a manifold `M` without boundary, carrying a smooth vector
field `v`, lies in an open set `U` such that the flow of `v` exists for a uniform time `ε > 0` on
`U` and is jointly continuous there. -/
theorem flow_box_local {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (v : (x : M) → TangentSpace (𝓡 n) x)
    (hv : ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M))) :
    ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > 0, ∃ Ψ : ℝ → M → M, IsFlowBox v ε U Ψ :=
  flow_box_local_aux v (fun x₀ ↦ contDiffAt_chartVF hv x₀)
    (fun x₀ _ _ _ h1 h2 h3 ↦ isMIntegralCurveOn_chartVF h1 h2 h3)

end Work.Morse
