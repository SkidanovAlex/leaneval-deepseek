import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Basic
import Submission.Work.PTGeometric.FDerivInChart
import Submission.Work.PTGeometric.regionNhdBoundaryZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.WeakRegion

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

set_option backward.isDefEq.respectTransparency false

/-- **Reading the weak hypotheses of the region-charting statement in the preferred chart at a boundary zero, at `C^∞` with the set-level smoothness conclusion.**

At a boundary zero `x` of `Φ` (a point of the boundary of the manifold with boundary `A` with
`Φ x = 0`) satisfying the sign condition (`Φ ≥ 0` on the boundary near `x`) and the tangency
condition (`mfderiv Φ x = c • (derivative of a boundary chart coordinate) x`, `c < 0`), the chart
expression `Ψ := Φ ∘ (extChartAt I x)⁻¹` of `Φ` vanishes at `p := extChartAt I x x`, `p` lies on
the boundary hyperplane, `Ψ` is `C^∞` on the fixed relative set `U ∩ {0 ≤ z 0}` for some open
`U ∋ p` (this is the set-level form, which the pointwise `ContDiffWithinAt ℝ ∞ Ψ _ p` does not give),
its within-derivative at `p` is `c • (z ↦ z 0)`, and it is nonnegative on the boundary hyperplane
near `p`.

This is the same content as the already-proven
`Work.PTGeometric.WeakRegion.exists_modelData_at_boundaryZero`
(`Submission/Work/PTGeometric/WeakRegion/exists_modelData_at_boundaryZero.lean`), with TWO changes:
the smoothness order is the smooth `∞` (that file is stated for `ω`, i.e. `⊤ : WithTop ℕ∞`, and
uses `(⊤ : WithTop ℕ∞)` for `Φ`, which the downstream development cannot provide), and the
smoothness conclusion is the *set-level* one `∃ U ∈ 𝓝 p, ContDiffOn ℝ ∞ Ψ (U ∩ range I)` (which is
what the graph result `exists_graph_halfSpace_cinf` needs; the pointwise version is not enough). The
existing file is a good template: copy it and (i) replace `(⊤ : WithTop ℕ∞)` by
`((⊤ : ℕ∞) : WithTop ℕ∞)` throughout (so the instance hypothesis is
`IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ A`, since `∞ < ⊤`), (ii) drop the
`IsManifold.maximalAtlas_subset_of_le (m := ∞) (n := ⊤) le_top he` step in the use of
`Work.PTGeometric.chartCoordMfderiv` (at `∞` the maximal atlas is the right one already), and
(iii) replace the smoothness step by the set-level transfer of
`OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff` together with
`contMDiffOn_iff_contDiffOn`: `Φ` is `ContMDiff I 𝓘(ℝ,ℝ) ∞` at EVERY point of `A`, so on a fixed
open `U' ∋ x` with `U' ⊆ (chartAt (EuclideanHalfSpace n) x).source` the chart expression
`Ψ = Φ ∘ (chartAt _ x).symm` is `ContDiffOn ℝ ∞ Ψ ((chartAt _ x).extend I) '' U'`, and the image is
a relative neighbourhood of `p` in the half-space. -/

theorem modelData_boundaryZero_cinf {n : ℕ} [NeZero n]
    {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace n) A]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ((⊤ : ℕ∞) : WithTop ℕ∞) A]
    {Φ : A → ℝ} (hΦ : ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) {x : A}
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace n).boundary A) (hx0 : Φ x = 0)
    (hsign : Filter.Eventually (fun y : A =>
        y ∈ (modelWithCornersEuclideanHalfSpace n).boundary A → 0 ≤ Φ y) (nhds x))
    (hone : ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace n)) (c : ℝ),
      e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace n)
        ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      x ∈ e.source ∧ c < 0 ∧
      (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (modelWithCornersEuclideanHalfSpace n).boundary A) ∧
      mfderiv (modelWithCornersEuclideanHalfSpace n) (modelWithCornersSelf ℝ ℝ) Φ x
        = c • mfderiv (modelWithCornersEuclideanHalfSpace n) (modelWithCornersSelf ℝ ℝ)
            (fun y : A => (e y).1 0) x) :
    ∃ (c : ℝ) (Ψ : EuclideanSpace ℝ (Fin n) → ℝ),
      c < 0 ∧
      (∀ y ∈ (extChartAt (modelWithCornersEuclideanHalfSpace n) x).source,
        Ψ (extChartAt (modelWithCornersEuclideanHalfSpace n) x y) = Φ y) ∧
      (extChartAt (modelWithCornersEuclideanHalfSpace n) x x).ofLp 0 = 0 ∧
      (∃ U ∈ nhds (extChartAt (modelWithCornersEuclideanHalfSpace n) x x),
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ
          (U ∩ Set.range (modelWithCornersEuclideanHalfSpace n))) ∧
      Ψ (extChartAt (modelWithCornersEuclideanHalfSpace n) x x) = 0 ∧
      fderivWithin ℝ Ψ (Set.range (modelWithCornersEuclideanHalfSpace n))
        (extChartAt (modelWithCornersEuclideanHalfSpace n) x x)
        = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0) ∧
      Filter.Eventually (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp 0 = 0 → 0 ≤ Ψ z)
        (nhdsWithin (extChartAt (modelWithCornersEuclideanHalfSpace n) x x)
          (Set.range (modelWithCornersEuclideanHalfSpace n))) := by
  classical
  set I := modelWithCornersEuclideanHalfSpace n with hI
  obtain ⟨e, c, he, hxe, hc, hzero_e, hdere⟩ := hone
  obtain ⟨ce, hce_pos, hce_eq⟩ := Work.PTGeometric.chartCoordMfderiv (n := n) e he hxe hxb
  set Ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun z => Φ ((extChartAt I x).symm z) with hΨ
  have hchartx : x ∈ (chartAt (EuclideanHalfSpace n) x).source := mem_chart_source _ _
  -- ## the set-level smoothness of the chart expression, via the chart bridge
  have hφ : (chartAt (EuclideanHalfSpace n) x) ∈ IsManifold.maximalAtlas I ∞ A :=
    IsManifold.chart_mem_maximalAtlas (I := I) x
  have hψ : (chartAt ℝ (Φ x)) ∈ IsManifold.maximalAtlas (𝓘(ℝ,ℝ)) ∞ ℝ := by
    rw [chartAt_self_eq]
    exact StructureGroupoid.mem_maximalAtlas_of_mem_groupoid (G := contDiffGroupoid ∞ (𝓘(ℝ,ℝ)))
      (StructureGroupoid.id_mem _)
  have hmaps : MapsTo Φ (chartAt (EuclideanHalfSpace n) x).source (chartAt ℝ (Φ x)).source := by
    intro y hy
    simp
  have hglob : ContMDiffOn I (𝓘(ℝ,ℝ)) ∞ Φ (chartAt (EuclideanHalfSpace n) x).source :=
    (contMDiffOn_univ.mpr hΦ).mono (subset_univ _)
  have h2 := (OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff (I := I) (J := 𝓘(ℝ,ℝ))
    (φ := chartAt (EuclideanHalfSpace n) x) (ψ := chartAt ℝ (Φ x)) (n := ∞)
    (f := Φ) (s := (chartAt (EuclideanHalfSpace n) x).source) hφ hψ (subset_refl _) hmaps).mpr hglob
  have hwritten : Ψ = (⇑((chartAt ℝ (Φ x) : OpenPartialHomeomorph ℝ ℝ).extend (𝓘(ℝ,ℝ))) ∘ Φ ∘
      ⇑((chartAt (EuclideanHalfSpace n) x).extend I).symm) := by
    funext z
    show Φ ((extChartAt I x).symm z) = (extChartAt (𝓘(ℝ,ℝ)) (Φ x)) (Φ ((extChartAt I x).symm z))
    rw [extChartAt_self_eq]
    rfl
  have h4 : ContDiffOn ℝ ∞ Ψ ((chartAt (EuclideanHalfSpace n) x).extend I ''
      (chartAt (EuclideanHalfSpace n) x).source) := by
    rw [hwritten]
    exact h2.contDiffOn
  refine ⟨c * ce, Ψ, mul_neg_of_neg_of_pos hc hce_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Ψ` agrees with `Φ` on the chart
    intro y hy
    show Φ ((extChartAt I x).symm ((extChartAt I x) y)) = Φ y
    rw [PartialEquiv.left_inv _ hy]
  · -- `p` lies on the boundary hyperplane
    have h := (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (m := n) (M := A) (e := chartAt (EuclideanHalfSpace n) x)
      (IsManifold.chart_mem_maximalAtlas (I := I) x) hchartx).mp hxb
    simpa only [extChartAt] using h
  · -- set-level smoothness on a relative neighbourhood of `p`
    have hset : (chartAt (EuclideanHalfSpace n) x).extend I ''
        (chartAt (EuclideanHalfSpace n) x).source = (extChartAt I x).target :=
      ((chartAt (EuclideanHalfSpace n) x).extend_target_eq_image_source (I := I)).symm
    have hmem : (chartAt (EuclideanHalfSpace n) x).extend I ''
        (chartAt (EuclideanHalfSpace n) x).source ∈
        𝓝[range I] ((extChartAt I x) x) :=
      hset.symm ▸ extChartAt_target_mem_nhdsWithin (I := I) x
    obtain ⟨U, hU, hUS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hmem
    exact ⟨U, hU, h4.mono hUS⟩
  · -- `Ψ` vanishes at `p`
    show Φ ((extChartAt I x).symm ((extChartAt I x) x)) = 0
    rw [extChartAt_to_inv]
    exact hx0
  · -- the within-derivative of `Ψ` at `p`, read through the preferred chart
    have hmd : MDifferentiableAt I (𝓘(ℝ,ℝ)) Φ x := hΦ.mdifferentiableAt (by simp)
    have hFD := Work.PTGeometric.hasFDerivWithinAt_comp_extChartAt_symm (I := I) (f := Φ)
      (x := x) hmd
    have hp_mem : (extChartAt I x) x ∈ range I :=
      extChartAt_target_subset_range (I := I) x (mem_extChartAt_target (I := I) x)
    have huniq : UniqueDiffWithinAt ℝ (range I) ((extChartAt I x) x) :=
      I.uniqueDiffOn.uniqueDiffWithinAt hp_mem
    have hder : fderivWithin ℝ Ψ (range I) ((extChartAt I x) x)
        = mfderiv I (𝓘(ℝ,ℝ)) Φ x := hFD.fderivWithin huniq
    rw [hder, hdere, hce_eq]
    ext v
    simp only [smul_apply, smul_eq_mul]
    ring_nf
  · -- the sign condition transfers along the chart
    have hcont : Tendsto (fun z : EuclideanSpace ℝ (Fin n) => (extChartAt I x).symm z)
        (𝓝[range I] ((extChartAt I x) x)) (𝓝 x) := by
      have hle : 𝓝[range I] ((extChartAt I x) x) ≤ 𝓝 ((extChartAt I x) x) := nhdsWithin_le_nhds
      have h := ((continuousAt_extChartAt_symm (I := I) x).tendsto).mono_left hle
      rwa [extChartAt_to_inv (I := I) x] at h
    filter_upwards [hcont.eventually hsign,
      extChartAt_target_mem_nhdsWithin (I := I) x] with z hzsign hztarget
    intro hz0
    refine hzsign ?_
    have hy_src : (extChartAt I x).symm z ∈ (chartAt (EuclideanHalfSpace n) x).source := by
      rw [← extChartAt_source I x]
      exact (extChartAt I x).map_target hztarget
    refine ((Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (m := n) (M := A) (e := chartAt (EuclideanHalfSpace n) x)
      (IsManifold.chart_mem_maximalAtlas (I := I) x) hy_src)).mpr ?_
    show ((extChartAt I x) ((extChartAt I x).symm z)).ofLp 0 = 0
    rw [PartialEquiv.right_inv _ hztarget]
    exact hz0

end Work.PTGeometric.WeakRegion
