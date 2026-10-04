import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.ChartBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! NOTE ON LOCATION.

The requested path of this lemma was `Submission/Work/Diff/EXT/Aux/chartMatFun_centre_posDef.lean`.
Lean 4.34 refuses to elaborate any file whose module name contains a component `Aux`
(`Lean/Elab/Import.lean`, `osForbiddenNames` contains `"AUX"`, compared case-insensitively):
`error: module name '...Aux...' is not portable: 'Aux' is a reserved file name on some operating
systems`.  So the file was moved to the portable directory `Auxiliary/`.  The *declaration name* is
unchanged: `Work.Diff.EXT.Aux.chartMatFun_centre_posDef`, and the namespace is kept as
`Work.Diff.EXT.Aux`. -/

set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.AuxL

/-- Bilinearity of a continuous linear form `T →L[ℝ] T →L[ℝ] ℝ` in both slots, in the shape needed
for the quadratic form of the chart matrix: the quadratic form of the matrix `(f (σ i) (σ j))ᵢⱼ`
is the value of `f` on the combination `∑ i, v i • σ i`. -/
private lemma sum_sum_mul_mul_inner {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {n : ℕ} (f : T →L[ℝ] T →L[ℝ] ℝ) (σ : Fin n → T) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * f (σ i) (σ j)) = f (∑ i, v i • σ i) (∑ i, v i • σ i) := by
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The chart matrix of a smooth metric is positive definite at the chart centre: for `y₀ = (extChartAt I x₀) x₀` and any nonzero coefficient vector `v`, `0 < ∑ i, ∑ j, v i * v j * chartMatFun g x₀ y₀ i j`.

Route: `(extChartAt I x₀).symm y₀ = x₀` (`PartialEquiv.left_inv`, using `mem_extChartAt_source`), then bilinearity of `g.inner x₀` turns the sum into `g.inner x₀ w w` with `w = ∑ i, v i • frameVector I x₀ x₀ (bB i)`; `w ≠ 0` from `Submission.ChartBounds.frameVector_eq_zero_iff` (`x₀ ∈ (chartAt H x₀).source`) and the fact that `bB` is a basis with `v ≠ 0`; conclude with the `pos` field of the Riemannian metric. -/
theorem chartMatFun_centre_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    (g : Submission.Diff.SMet I M) (x₀ : M)
    (v : Fin (Module.finrank ℝ E) → ℝ) (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ ((extChartAt I x₀) x₀) i j := by
  classical
  -- register the metric `g` as the Riemannian structure on the tangent bundle, so that the
  -- tangent spaces at the chart centre carry the inner product induced by `g`
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- unfold the chart matrix at the chart centre, where the inverse chart returns `x₀`
  have hc : (∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ ((extChartAt I x₀) x₀) i j)
      = ∑ i, ∑ j, v i * v j *
          g.inner x₀ (Submission.Geodesic.frameVector (I := I) x₀ x₀ (Work.Diff.EXT.bB (E := E) i))
            (Submission.Geodesic.frameVector (I := I) x₀ x₀ (Work.Diff.EXT.bB (E := E) j)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Work.Diff.EXT.chartMatFun, extChartAt_to_inv]
  -- bilinearity of `g.inner x₀` turns the double sum into the quadratic form of the combination
  rw [hc, sum_sum_mul_mul_inner (f := g.inner x₀)
    (σ := fun i => Submission.Geodesic.frameVector (I := I) x₀ x₀ (Work.Diff.EXT.bB (E := E) i)) v]
  -- linearity of the frame vector in its coordinate vector
  have hlin : (∑ i, v i •
        Submission.Geodesic.frameVector (I := I) x₀ x₀ (Work.Diff.EXT.bB (E := E) i))
      = Submission.Geodesic.frameVector (I := I) x₀ x₀
          (∑ i, v i • Work.Diff.EXT.bB (E := E) i) := by
    have h := Submission.Geodesic.frameVector_sum (I := I) Finset.univ x₀ x₀ v
      (fun i => Work.Diff.EXT.bB (E := E) i)
    simpa using h.symm
  rw [hlin]
  -- the combination is nonzero because `bB` is a basis and `v ≠ 0`
  refine g.pos x₀ _ ?_
  intro hzero
  have ha : (∑ i, v i • Work.Diff.EXT.bB (E := E) i) = 0 :=
    (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := x₀) (p := x₀)
      (mem_chart_source H x₀) _).mp hzero
  have hli : ∀ i, v i = 0 :=
    (Fintype.linearIndependent_iff.mp (Work.Diff.EXT.bB (E := E)).linearIndependent) v ha
  exact hv (funext fun i => by simpa using hli i)

end Work.Diff.EXT.AuxL
