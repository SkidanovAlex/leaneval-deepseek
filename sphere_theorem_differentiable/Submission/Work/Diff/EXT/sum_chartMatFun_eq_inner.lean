import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped BigOperators

/-- Bilinearity of a continuous linear form `T →L[ℝ] T →L[ℝ] ℝ` in both slots, in the shape needed
for the quadratic form of the chart matrix. -/
lemma sum_sum_mul_mul_inner {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {n : ℕ} (f : T →L[ℝ] T →L[ℝ] ℝ) (σ : Fin n → T) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * f (σ i) (σ j)) = f (∑ i, v i • σ i) (∑ i, v i • σ i) := by
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The quadratic form of the chart matrix is the metric of the combination.**
For a smooth metric `g`, a chart centre `x₀`, a chart coordinate `y : E` (write `p = (extChartAt I x₀).symm y`)
and coefficients `v : Fin (Module.finrank ℝ E) → ℝ`,
`∑ i, ∑ j, v i * v j * chartMatFun g x₀ y i j = g.inner p (∑ i, v i • σ i) (∑ i, v i • σ i)`
where `σ i = frameVector I x₀ p (bB i)` is the coordinate frame of the chart at `x₀`.
This is pure bilinearity of `g.inner p : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ`
(`map_sum`, `map_smul` in both slots) plus `Finset.sum_comm`; no manifold topology and, in particular,
no `T2Space M` and no `I.Boundaryless` is needed. -/
theorem sum_chartMatFun_eq_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) (v : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ y i j)
      = g.inner ((extChartAt I x₀).symm y)
          (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i))
          (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i)) := by
  -- the metric form `g.inner p` is a *continuous* linear map in each slot once the metric is
  -- installed as the Riemannian-bundle instance; without it the type class search for
  -- `TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ` on the fibres fails
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have key : (∑ i, ∑ j, v i * v j * (g.inner ((extChartAt I x₀).symm y)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB (E := E) j))))
      = g.inner ((extChartAt I x₀).symm y)
          (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (bB (E := E) i))
          (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (bB (E := E) i)) := by
    -- linearity of the metric form in its second slot
    have h3 : ∀ u : TangentSpace I ((extChartAt I x₀).symm y),
        g.inner ((extChartAt I x₀).symm y) u
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
              ((extChartAt I x₀).symm y) (bB (E := E) i))
          = ∑ i, v i * (g.inner ((extChartAt I x₀).symm y) u
              (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
                (bB (E := E) i))) := by
      intro u
      rw [map_sum]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    -- linearity of the metric form in its first slot
    have h2 : ∀ w : TangentSpace I ((extChartAt I x₀).symm y),
        g.inner ((extChartAt I x₀).symm y)
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
              ((extChartAt I x₀).symm y) (bB (E := E) i)) w
          = ∑ i, v i * (g.inner ((extChartAt I x₀).symm y)
              (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
                (bB (E := E) i)) w) := by
      intro w
      rw [map_sum, ContinuousLinearMap.sum_apply]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [h2 (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
      ((extChartAt I x₀).symm y) (bB (E := E) i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h3 (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (bB (E := E) i)), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simpa only [chartMatFun] using key

end Work.Diff.EXT
