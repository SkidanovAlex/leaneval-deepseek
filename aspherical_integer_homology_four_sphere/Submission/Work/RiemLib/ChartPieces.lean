import Submission.Work.RiemLib.GeodesicGlobal
import Submission.Work.RiemLib.CurveField
import Submission.Work.RiemLib.Commons.Topology.Order.exists_partition_subordinate_Icc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A finite partition of an interval on which a geodesic is covered by chart data

For a geodesic `γ` which is `C^∞` and geodesic on an open set `V` containing the closed interval
`[a,b]`, with non-vanishing velocity, there is a partition `a = c 0 < … < c N = b` of `[a,b]`, a
chart centre `x k` and an open interval `Ioo (A k) (B k)` *containing* `[c k, c (k+1)]` with room, on
which the coordinate curve `t ↦ (extChartAt I (x k)) (γ t)` satisfies the chart geodesic equation.

The construction: `GeodesicGlobal.chartODE_of_isGeodesic` gives the local data at every point of
`[a,b]`; the family of intervals `Ioo (t-δ t) (t+δ t)` is an open cover of `[a,b]`, one extracts a
finite subcover, and
`Commons.Topology.Order.exists_partition_subordinate_Icc` produces a partition subordinate to it.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

namespace Submission.ChartPieces

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

open Classical in
/-- **The chart pieces of a geodesic.** -/
theorem exists_chart_pieces
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {a b : ℝ}
    (hab : a ≤ b) (hVab : Icc a b ⊆ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeo : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0) :
    ∃ N : ℕ, ∃ c : ℕ → ℝ, c 0 = a ∧ c N = b ∧ (∀ k < N, c k < c (k + 1)) ∧
      ∃ x : ℕ → M, ∃ A B : ℕ → ℝ,
        (∀ k < N, A k < c k ∧ c (k + 1) < B k) ∧
        (∀ k < N, ∀ t ∈ Ioo (A k) (B k), γ t ∈ (chartAt H (x k)).source) ∧
        (∀ k < N, ∀ t ∈ Ioo (A k) (B k),
          HasDerivAt (fun r => (extChartAt I (x k)) (γ r))
            (deriv (fun r => (extChartAt I (x k)) (γ r)) t) t ∧
          HasDerivAt (deriv (fun r => (extChartAt I (x k)) (γ r)))
            (chartGeodesicVectorField cov (x k) ((extChartAt I (x k)) (γ t),
              deriv (fun r => (extChartAt I (x k)) (γ r)) t)) t) := by
  -- the local chart data at every point of `[a,b]`
  have hloc : ∀ t : ℝ, ∃ δ : ℝ, t ∈ Icc a b → 0 < δ ∧
      (∀ s ∈ Ioo (t - δ) (t + δ), γ s ∈ (chartAt H (γ t)).source) ∧
      (∀ s ∈ Ioo (t - δ) (t + δ),
        HasDerivAt (fun r => (extChartAt I (γ t)) (γ r))
          (deriv (fun r => (extChartAt I (γ t)) (γ r)) s) s) ∧
      (∀ s ∈ Ioo (t - δ) (t + δ),
        HasDerivAt (deriv (fun r => (extChartAt I (γ t)) (γ r)))
          (chartGeodesicVectorField cov (γ t) ((extChartAt I (γ t)) (γ s),
            deriv (fun r => (extChartAt I (γ t)) (γ r)) s)) s) := by
    intro t
    by_cases ht : t ∈ Icc a b
    · have htV : t ∈ V := hVab ht
      obtain ⟨Z, hZ, hZeq⟩ :=
        Submission.CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity
          (I := I) hV htV hγ (hne t htV)
      obtain ⟨δ, hδ, h1, -, h3, h4⟩ :=
        Submission.GeodesicGlobal.chartODE_of_isGeodesic (cov := cov) (γ t) hV htV hγ
          (mem_chart_source H (γ t)) (fun s hs => hgeo s hs) Z hZ hZeq
      exact ⟨δ, fun _ => ⟨hδ, h1, h3, h4⟩⟩
    · exact ⟨1, fun h => absurd h ht⟩
  choose δ hδ using hloc
  -- the induced open cover of `[a,b]`, and a finite subcover
  have hcov : Icc a b ⊆ ⋃ t : {x : ℝ // x ∈ Icc a b}, Ioo ((t : ℝ) - δ t) ((t : ℝ) + δ t) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    simp only [Set.mem_Ioo]
    exact ⟨by linarith [(hδ x hx).1], by linarith [(hδ x hx).1]⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : {x : ℝ // x ∈ Icc a b} => Ioo ((t : ℝ) - δ t) ((t : ℝ) + δ t))
    (fun _ => isOpen_Ioo) hcov
  -- the partition lemma
  obtain ⟨N, c, hc0, hcN, hmono, hpiece⟩ :=
    Commons.Topology.Order.exists_partition_subordinate_Icc
      (U := fun i : {t : {x : ℝ // x ∈ Icc a b} // t ∈ s} =>
        Ioo (((i : {x : ℝ // x ∈ Icc a b}) : ℝ) - δ i) (((i : {x : ℝ // x ∈ Icc a b}) : ℝ) + δ i))
      (fun _ => isOpen_Ioo) hab (by
        intro x hx
        obtain ⟨t, hts, hxt⟩ := Set.mem_iUnion₂.mp (hs hx)
        exact Set.mem_iUnion.mpr ⟨⟨t, hts⟩, hxt⟩)
  have hex : ∀ k : ℕ, ∃ i : {t : {x : ℝ // x ∈ Icc a b} // t ∈ s},
      k < N → Icc (c k) (c (k + 1)) ⊆
        Ioo (((i : {x : ℝ // x ∈ Icc a b}) : ℝ) - δ i) (((i : {x : ℝ // x ∈ Icc a b}) : ℝ) + δ i) := by
    intro k
    by_cases hk : k < N
    · obtain ⟨i, hi⟩ := hpiece k hk
      exact ⟨i, fun _ => hi⟩
    · have hsne : s.Nonempty := by
        obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp (hs (left_mem_Icc.mpr hab : a ∈ Icc a b))
        exact ⟨i, hi⟩
      obtain ⟨t₀, ht₀⟩ := hsne
      exact ⟨⟨t₀, ht₀⟩, fun h => absurd h hk⟩
  choose w hw using hex
  refine ⟨N, c, hc0, hcN, hmono, fun k => γ (((w k).val : {x : ℝ // x ∈ Icc a b}) : ℝ),
    fun k => (((w k).val : {x : ℝ // x ∈ Icc a b}) : ℝ)
      - δ ((w k).val : {x : ℝ // x ∈ Icc a b}),
    fun k => (((w k).val : {x : ℝ // x ∈ Icc a b}) : ℝ)
      + δ ((w k).val : {x : ℝ // x ∈ Icc a b}), ?_, ?_, ?_⟩
  · intro k hk
    have h := hw k hk
    exact ⟨by linarith [(Set.mem_Ioo.mp (h (left_mem_Icc.mpr (hmono k hk).le))).1],
      by linarith [(Set.mem_Ioo.mp (h (right_mem_Icc.mpr (hmono k hk).le))).2]⟩
  · intro k hk t ht
    exact (hδ ((w k).val : {x : ℝ // x ∈ Icc a b}) (w k).val.2).2.1 t ht
  · intro k hk t ht
    exact ⟨(hδ ((w k).val : {x : ℝ // x ∈ Icc a b}) (w k).val.2).2.2.1 t ht,
      (hδ ((w k).val : {x : ℝ // x ∈ Icc a b}) (w k).val.2).2.2.2 t ht⟩

end

end Submission.ChartPieces
