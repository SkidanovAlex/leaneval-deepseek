import Mathlib
import Submission.Work.Diff.STE.B3.CompSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: a uniform positive lower bound for the chart volume density

`D.DensGood i` says that the volume density `D.dens i = √det (Gram of the coordinate frame)` is
*pointwise* positive and smooth on the chart target of `x₀ i`.  For the pointwise control of a
section by the composite norm (`B3/Pointwise.lean`) one needs the *uniform* statement: a single
`d₀ > 0` which bounds `D.dens i z` from below for every chart `i` and every flat coordinate `z`
in the closed ball of radius `2 * D.σ i`.

This is a compactness argument.  The ball of radius `2 σ i` in the flat coordinates is compact
(finite dimension), it is contained in the chart target (`D.htarget`), and on it `D.dens i` is
continuous and positive by `hd`; hence its minimum is attained and positive.  Since `ι₀` is finite,
the (finite) minimum over the charts is positive as well; equivalently, we may first show the
per-chart statement and then take a finite infimum over a `Finset` (done by induction on the
finset, which also disposes of the empty index type).
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

/-- **Per-chart uniform lower bound.**  On the compact flat ball of radius `2 σ i` the volume
density is continuous (`hd i`) and strictly positive (at every point of the ball the flat
coordinate lies in the chart target, by `D.htarget`), so it attains a strictly positive minimum
there. -/
lemma dens_lower_bound_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hd : ∀ i : ι₀, D.DensGood i) (i : ι₀) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ i → m ≤ D.dens i z := by
  classical
  -- membership in the closed flat ball of radius `2 σ i` is the hypothesis of the statement
  have hmem : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i) ↔
        ‖z‖ ≤ 2 * D.σ i := by
    intro z
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hKc : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i)) :=
    isCompact_closedBall _ _
  have hKne : (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i)).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (by linarith [D.hσ i])⟩
  -- on the ball, the density is continuous (its flat coordinate lies in the chart target)
  have hcont : ContinuousOn (D.dens i)
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i)) := by
    intro z hz
    have hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
      D.htarget i z ((hmem z).mp hz)
    exact ((hd i z hzt).2).continuousAt.continuousWithinAt
  obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn hKne hcont
  have hz₀t : flatToE (I := I) (D.x₀ i) z₀ ∈ (extChartAt I (D.x₀ i)).target :=
    D.htarget i z₀ ((hmem z₀).mp hz₀)
  exact ⟨D.dens i z₀, (hd i z₀ hz₀t).1, fun z hz => hmin ((hmem z).mpr hz)⟩

/-- **Uniform lower bound over a finite set of charts.**  Induction on the finset: the empty
finset is trivial, and the insert step takes the minimum of the two constants. -/
lemma dens_lower_bound_finset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hd : ∀ i : ι₀, D.DensGood i) (s : Finset ι₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ i ∈ s, ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
      obtain ⟨d, hdpos, hdle⟩ := ih
      obtain ⟨m, hmpos, hmle⟩ := dens_lower_bound_chart D hd a
      refine ⟨min d m, lt_min hdpos hmpos, fun i hi z hz => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact le_trans (min_le_right _ _) (hmle z hz)
      · exact le_trans (min_le_left _ _) (hdle i hi' z hz)

theorem dens_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hd : ∀ i : ι₀, D.DensGood i) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z := by
  obtain ⟨d₀, hdpos, hdle⟩ := dens_lower_bound_finset D hd Finset.univ
  exact ⟨d₀, hdpos, fun i z hz => hdle i (Finset.mem_univ i) z hz⟩

end Work.Diff.STE.B3
