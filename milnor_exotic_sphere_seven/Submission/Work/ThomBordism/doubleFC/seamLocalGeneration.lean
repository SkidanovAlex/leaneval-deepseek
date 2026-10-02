import Mathlib
import Submission.Work.ThomBordism.doubleFC.defs
import Submission.Work.ThomBordism.doubleFC.seam_mem_closure_interior
import Submission.Work.ThomBordism.doubleFC.span_relLocClass_iff_of_isZero
import Submission.Work.ThomBordism.localClassAt
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Cohomology.capped_localDegree_generator
import Submission.Work.Cohomology.localHomology
import Submission.Work.ThomBordism.doubleChartedT2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism.doubleFC

noncomputable section

/-- **Vanishing of `H_*(X∖{z}, X∖K)` for a chart ball `K` around the centre `c`.**

This is `Work.Cohomology.isZero_relSubPunctured` without the (unused) compactness hypothesis on `X`
and with an arbitrary point `z ∈ K` rather than only the centre `c`: the chart ball
`K = e⁻¹'closedBall (e c) (r/2) ∩ e.source` (`e = chartAt _ c`) is a compact convex set in the chart,
so `Work.Cohomology.isZero_relChains_punctured_chart` gives the acyclicity of the honest relative
complex `C_*(X∖{z}, X∖K)`, and `Work.Cohomology.relSubPunctured_homology_iso` transports it to the
`coker (inclChainsSub …)` model in which the triple sequence is stated. -/
theorem isZero_relSubPunctured_chart {N : ℕ} (hN : 1 ≤ N) (X : TopCat) [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) X] (c : X) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin N)) := chartAt _ c
    Metric.ball (e c) r ⊆ e.target →
    let K : Set X := e ⁻¹' Metric.closedBall (e c) (r / 2) ∩ e.source
    ∀ (z : X) (hzK : z ∈ K), ∀ i, IsZero ((cokernel
      (Work.Cohomology.inclChainsSub X Kᶜ ({z} : Set X)ᶜ
        (fun q hq hqz => hq (Set.mem_singleton_iff.mp hqz ▸ hzK)))).homology i) := by
  intro e hball K z hzK i
  obtain ⟨eiso⟩ := Work.Cohomology.relSubPunctured_homology_iso X z K hzK i
  refine IsZero.of_iso ?_ eiso
  refine Work.Cohomology.isZero_relChains_punctured_chart N hN X c r hr
    (Metric.closedBall (e c) (r / 2)) (isCompact_closedBall _ _)
    (convex_closedBall _ _) hball ?_ z ?_ i
  · intro v hv
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hv
    linarith
  · exact hzK

/-- **Local generation at a seam point of the double, given generation at the interior points of
the first copy.**

The seam point `x = doubleιM b.1` is approached by interior points of the first copy
(`Work.ThomBordism.doubleFC.seam_mem_closure_interior`); inside a chart ball `K` of the double at `x`
(whose punctured complement is acyclic, `isZero_relSubPunctured_chart`) pick an interior point
`z = interiorEmb u ∈ K`.  The two transfers
`Work.ThomBordism.doubleFC.span_relLocClass_iff_of_isZero` (for the pairs `(z, K)` and `(x, K)`)
move the generation hypothesis from `z` to the set `K` and from `K` to `x`. -/
theorem seamLocalGeneration (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.ThomBordism.Double n M))).homology (n + 1))
    (hgenM : ∀ (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
      Submodule.span ℤ {(Work.ThomBordism.localClassAt (TopCat.of (Work.ThomBordism.Double n M)) (n + 1) cD
        (Work.ThomBordism.doubleιM (n := n) (M := M) y))} = ⊤)
    (b : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    Submodule.span ℤ {(Work.ThomBordism.localClassAt (TopCat.of (Work.ThomBordism.Double n M)) (n + 1) cD
      (Work.ThomBordism.doubleιM (n := n) (M := M) b.1))} = ⊤ := by
  classical
  haveI hC : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (Double n M) :=
    doubleChartedSpace (n := n) (M := M)
  haveI hT2 : T2Space (Double n M) := DblT2.t2Space_double (n := n) (M := M)
  have hN : 1 ≤ n + 1 := Nat.le_add_left 1 n
  -- the seam point
  set x : Double n M := doubleιM (n := n) (M := M) b.1 with hx
  -- the preferred chart of the double at `x` and a ball around `e x` inside its target
  set e : OpenPartialHomeomorph (Double n M) (EuclideanSpace ℝ (Fin (n + 1))) :=
    chartAt (EuclideanSpace ℝ (Fin (n + 1))) x with he
  have hxe : e x ∈ e.target := by rw [he]; exact mem_chart_target _ x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) hxe
  -- the chart ball
  set K : Set (Double n M) := e ⁻¹' Metric.closedBall (e x) (r / 2) ∩ e.source with hK
  have hxK : x ∈ K := by
    rw [hK]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, Metric.mem_closedBall, dist_self]
      linarith
    · rw [he]; exact mem_chart_source _ x
  -- `K` is a neighbourhood of `x`
  have hUopen : IsOpen (e ⁻¹' Metric.ball (e x) (r / 2) ∩ e.source) := by
    rw [Set.inter_comm]
    exact e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hxU : x ∈ e ⁻¹' Metric.ball (e x) (r / 2) ∩ e.source := by
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, Metric.mem_ball, dist_self]
      linarith
    · rw [he]; exact mem_chart_source _ x
  have hKnhds : K ∈ nhds x := by
    rw [hK]
    exact Filter.mem_of_superset (hUopen.mem_nhds hxU)
      (fun v hv => ⟨Metric.ball_subset_closedBall hv.1, hv.2⟩)
  -- the seam point is a limit of interior points of the first copy
  have hxcl : x ∈ closure (Set.range (interiorEmb (n := n) (M := M))) := by
    rw [hx]
    exact seam_mem_closure_interior n M b
  obtain ⟨z, hzK, hzr⟩ := mem_closure_iff_nhds.mp hxcl K hKnhds
  obtain ⟨u, rfl⟩ := hzr
  -- generation at the interior point `z = interiorEmb u`
  have hgenz : Submodule.span ℤ {(Work.Cohomology.relLocClass (TopCat.of (Double n M)) (n + 1) cD
      ({interiorEmb (n := n) (M := M) u} : Set (Double n M)))} = ⊤ := by
    rw [Work.Cohomology.relLocClass_singleton]
    exact hgenM u.1 u.2
  -- vanishing of the punctured chart-ball pair at every point of `K`
  have hvan : ∀ (w : Double n M) (hw : w ∈ K), ∀ i, IsZero ((cokernel
      (Work.Cohomology.inclChainsSub (TopCat.of (Double n M)) Kᶜ ({w} : Set (Double n M))ᶜ
        (fun q hq hqw => hq (Set.mem_singleton_iff.mp hqw ▸ hw)))).homology i) :=
    fun w hw i => isZero_relSubPunctured_chart hN (TopCat.of (Double n M)) x r hr hball w hw i
  -- transfer the generation from the point `z` to the set `K`
  have hKgen : Submodule.span ℤ {Work.Cohomology.relLocClass (TopCat.of (Double n M)) (n + 1) cD K} = ⊤ :=
    (span_relLocClass_iff_of_isZero (X := TopCat.of (Double n M)) (N := n + 1) cD
      (K := K) (z := interiorEmb (n := n) (M := M) u) hzK
      (hvan (interiorEmb (n := n) (M := M) u) hzK)).mpr hgenz
  -- and from the set `K` to the point `x`
  have hxgen : Submodule.span ℤ {(Work.Cohomology.relLocClass (TopCat.of (Double n M)) (n + 1) cD
      ({x} : Set (Double n M)))} = ⊤ :=
    (span_relLocClass_iff_of_isZero (X := TopCat.of (Double n M)) (N := n + 1) cD
      (K := K) (z := x) hxK (hvan x hxK)).mp hKgen
  rw [Work.Cohomology.relLocClass_singleton (TopCat.of (Double n M)) (n + 1) cD x] at hxgen
  exact hxgen

end

end Work.ThomBordism.doubleFC
