import Mathlib
import Submission.Work.Morse.flow_basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology

/-- The chart expression of a smooth vector field is `C¹` at the image of the base point.

Given a vector field `v` on a `C^∞` manifold `M` with model `EuclideanSpace ℝ (Fin n)`, whose
associated section of the tangent bundle is `C^∞`, the chart expression `chartVF v x₀` of `v` in the
chart at `x₀` is `C¹` at the image `extChartAt (𝓡 n) x₀ x₀` of the base point. -/
theorem contDiffAt_chartVF {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {v : (x : M) → TangentSpace (𝓡 n) x}
    (hv : ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M)))
    (x₀ : M) : ContDiffAt ℝ 1 (chartVF v x₀) (extChartAt (𝓡 n) x₀ x₀) := by
  -- The point `x₀` lies in the base set (= source of the chart at `x₀`) of the tangent
  -- trivialization at `x₀`.
  have hmem : x₀ ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀).baseSet :=
    mem_chart_source _ x₀
  -- Rewrite the smoothness of the section in terms of the tangent bundle structure.
  have hsec : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M)) x₀ := by
    simpa only [ModelWithCorners.tangent] using hv x₀
  -- The trivialization coordinate expression of the section is smooth at `x₀`.
  have hw := ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀).contMDiffAt_section_iff
      hmem).mp hsec
  -- Read the smoothness in the preferred chart at `x₀` (i.e. compose with `(extChartAt ..).symm`).
  have hw2 := (contMDiffAt_iff_source (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))).mp hw
  have hw3 := (contMDiffWithinAt_iff_contDiffWithinAt).mp hw2
  -- The model `𝓡 n` is boundaryless, so `range (𝓡 n) = univ`.
  rw [ModelWithCorners.range_eq_univ] at hw3
  have hw4 := (contDiffWithinAt_univ.mp hw3).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  -- The chart expression `chartVF v x₀` is exactly the trivialization coordinate expression
  -- composed with `(extChartAt (𝓡 n) x₀).symm`.
  rwa [show ((fun x ↦ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀
        ⟨x, v x⟩).2) ∘ (extChartAt (𝓡 n) x₀).symm) = chartVF v x₀ from by
      funext y
      simp only [Function.comp_apply, chartVF, tangentCoordChange_def,
        TangentBundle.trivializationAt_apply, extChartAt]] at hw4

end Work.Morse
