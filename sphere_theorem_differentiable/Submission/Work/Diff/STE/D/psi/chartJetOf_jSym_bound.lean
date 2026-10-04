import Mathlib
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.D.ChartData_jVec
import Submission.Work.Diff.STE.D.ChartData_genMap
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform bound on the chart `2`-jets of the symmetrised Galerkin family

`Work.Diff.STE.D.chartJetOf h x₀ y` is the spatial `2`-jet (value, first and second Fréchet
derivative in the chart coordinate) of the chart matrix of a section `h`.  The target theorem
`chartJetOf_jSym_bound` states that on any compact set `K` inside the chart target of `x₀`, the
norms of the jets of the *whole* symmetrised spanning family `jSym D ε z`, `z` ranging over the
finite index set `JIdx`, are bounded by a single constant.

Two ingredients:

* every `jSym D ε z` has smooth chart data (`jSym_chartData`, from `ChartData_genMap`), so its
  spatial `2`-jet is `C^∞` in the chart coordinate (`contDiffOn_chartJetOf`);
* a continuous function is bounded on a compact subset of an open set
  (`chartJetOf_bound_of_chartData`), and the index set `JIdx` is finite, so the finitely many
  bounds can be summed.
-/

namespace Work.Diff.STE.D.psi

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]

noncomputable section

/-- **Every symmetrised spanning vector of the Galerkin family has smooth chart data.**
`jSym D ε z = jFamily D ε z + jFamily D ε (idxSwap ε z)` is a sum of two spanning vectors
`jVec D ε i a b q`, each of which has smooth chart data (`GenMap.jVec_chartData`), and `ChartData`
is preserved by addition. -/
lemma jSym_chartData {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) := by
  have h1 := Work.Diff.STE.D.GenMap.jVec_chartData (I := I) (M := M) D ε
    z.1 z.2.1 z.2.2.1 z.2.2.2
  have h2 := Work.Diff.STE.D.GenMap.jVec_chartData (I := I) (M := M) D ε
    (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z).1
    (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z).2.1
    (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.1
    (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.2
  rw [Work.Diff.STE.D.jSym]
  refine Work.Diff.STE.D.GenMap.chartData_add (I := I) (M := M) ?_ ?_
  · simpa only [Work.Diff.STE.B3.jFamily] using h1
  · simpa only [Work.Diff.STE.B3.jFamily] using h2

/-- **The spatial `2`-jet of the chart matrix is bounded on a compact subset of the chart target.**
The chart data of `h` says that the chart matrix is `C^∞` on the chart target; hence so is its
spatial `2`-jet (`contDiffOn_chartJetOf`), and a continuous function is bounded on a compact set. -/
lemma chartJetOf_bound_of_chartData (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (K : Set E) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x₀).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E, y ∈ K →
      ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((contDiffOn_chartJetOf (I := I) (M := M) h x₀ (hh x₀)).continuousOn.mono hKt)
  exact ⟨max 0 C, le_max_left 0 C, fun y hy => le_trans (hC y hy) (le_max_right 0 C)⟩

theorem chartJetOf_jSym_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (K : Set E)
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x₀).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) (y : E),
      y ∈ K → ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M)
        (jSym (I := I) (M := M) D ε z) x₀ y‖ ≤ C := by
  classical
  -- Each individual member of the family is bounded on `K` by compactness.
  have hbd : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E, y ∈ K →
        ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M)
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀ y‖ ≤ C :=
    fun z => chartJetOf_bound_of_chartData (I := I) (M := M)
      (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀
      (jSym_chartData (I := I) (M := M) D ε z) K hK hKt
  choose Cz hCz0 hCz using hbd
  -- The index set is finite, so the finitely many bounds can be summed.
  refine ⟨∑ z, Cz z, Finset.sum_nonneg (fun z _ => hCz0 z), fun z y hy => ?_⟩
  exact le_trans (hCz z y hy)
    (Finset.single_le_sum (fun w _ => hCz0 w) (Finset.mem_univ z))

end

end Work.Diff.STE.D.psi
