import Mathlib
import Submission.Work.OddBound.PiExtChart
import Submission.Work.OddBound.design.PiExtManifold

namespace Work.OddBound

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField

/-!
Every chart of the atlas of `piChartedSpaceExt` is a product of individual extended charts.

The atlas of `piChartedSpace` is `OpenPartialHomeomorph.pi '' Set.pi univ (fun _ => atlas _ _)`
by definition, and the atlas of `chartedSpaceExtChart` is `Set.range (extChartHomeo (I := I))`.
So a chart of the atlas is `OpenPartialHomeomorph.pi f` with `f i = extChartHomeo (I := I) (x i)`
for some `x i : M` at every index `i`; choosing the `x i` gives `f = fun i => extChartHomeo (x i)`,
i.e. the chart is `piExtChart x`.  All the set-theoretic steps are definitional (`atlas` is an
`abbrev` for the `ChartedSpace.atlas` projection), which is why `he` can be retyped directly.
-/

theorem exists_piExtChart_eq_of_mem_atlas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {N : ℕ} {e : OpenPartialHomeomorph (Fin (N - 1) → M) ((Fin (N - 1)) → E)}
    (he : e ∈ @atlas ((Fin (N - 1)) → E) _ ((Fin (N - 1)) → M) _
      (Work.OddBound.piChartedSpaceExt (I := I) N)) :
    ∃ x : Fin (N - 1) → M, e = Work.OddBound.piExtChart (I := I) x := by
  -- the atlas of `piChartedSpaceExt` is, definitionally, the set of products of extended charts
  have he' : e ∈ OpenPartialHomeomorph.pi ''
      (Set.pi univ fun _ : Fin (N - 1) => Set.range (Work.OddBound.extChartHomeo (I := I))) := he
  rcases (Set.mem_image _ _ _).1 he' with ⟨f, hf, hef⟩
  have hf : ∀ i, f i ∈ Set.range (Work.OddBound.extChartHomeo (I := I)) :=
    fun i => hf i (Set.mem_univ i)
  choose x hx using fun i => Set.mem_range.1 (hf i)
  refine ⟨x, ?_⟩
  rw [← hef, funext fun i => (hx i).symm]
  rfl

end Work.OddBound
