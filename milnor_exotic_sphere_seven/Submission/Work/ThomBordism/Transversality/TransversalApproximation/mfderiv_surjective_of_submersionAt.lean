import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Surjectivity of `mfderiv` for submersions at interior points

Mathlib's `Manifold.IsSubmersionAt` is defined by a local normal form (in suitable charts, `f`
looks like `(u, v) ↦ u`).  Its relation to surjectivity of `mfderiv` is an explicit TODO of
`Mathlib/Geometry/Manifold/Submersion.lean`.  Here we prove that direction at an interior point.

The mathematical content is standard: the local normal form `(u, v) ↦ u` has surjective
differential, and the chart transitions have invertible differentials.  The formal work is the
chart bookkeeping; besides that one needs the (chart-independent) description of interior points
for charts lying in the *maximal* atlas rather than in the given atlas.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

/-- **Chart-independence of interior points, for the maximal atlas.**
If `e` and `e'` are two charts in the maximal atlas around `x`, then `e` maps `x` into the
interior of its own target iff `e'` does.

This is `ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas` with the
hypotheses weakened from `atlas H M` to `maximalAtlas I n M` (the proof only ever uses the latter,
via `IsManifold.subset_maximalAtlas`). -/
lemma mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M] {e e' : OpenPartialHomeomorph M H}
    {x : M} (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := I.contDiffOn_extendCoordChange he he'
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) →
      e'.extend I x ∈ interior (range I) by
    refine e'.mem_interior_extend_target (by simp [hex']) <| h ?_
    exact (I.isInvertible_fderivWithin_extendCoordChange hn he he' <| by simp [hex, hex']).surjective
  intro hφx'
  wlog hk : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField hk]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and,
      e'.extend_source]
    exact e.extend_preimage_mem_nhds hex <| e'.open_source.mem_nhds hex'
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := ℝ),
    (hφ.differentiableOn hn _ (by simp [φ, hex, hex'])).restrictScalars_fderivWithin (𝕜 := ℝ)
      (uniqueDiffWithinAt_of_mem_nhds hφx), fderivWithin_of_mem_nhds <| hφx] at hφx'
  rw [show e'.extend I x = φ (e.extend I x) by simp [φ, hex]]
  replace hφ := ((hφ.restrict_scalars ℝ).differentiableOn hn).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

/-- The `iff` form of `mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas`. -/
lemma mem_interior_range_iff_of_mem_maximalAtlas
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M] {e e' : OpenPartialHomeomorph M H}
    {x : M} (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) (hex : x ∈ e.source) (hex' : x ∈ e'.source) :
    e.extend I x ∈ interior (e.extend I).target ↔
    e'.extend I x ∈ interior (e'.extend I).target :=
  ⟨fun h ↦ mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas hn he he' hex hex' h,
   fun h ↦ mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas hn he' he hex' hex h⟩

/-- A point of a `C¹` manifold is an interior point iff it is sent into the interior of the target
by any chart of the maximal atlas around it. -/
lemma isInteriorPoint_iff_of_mem_maximalAtlas
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M] {e : OpenPartialHomeomorph M H}
    {x : M} (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  rw [ModelWithCorners.isInteriorPoint_iff]
  exact mem_interior_range_iff_of_mem_maximalAtlas hn (IsManifold.chart_mem_maximalAtlas x) he
    (mem_chart_source H x) hx

theorem mfderiv_surjective_of_submersionAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {k : ℕ}
    {f : M → EuclideanSpace ℝ (Fin k)} {x : M} (hx : I.IsInteriorPoint x)
    (h : Manifold.IsSubmersionAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f x) :
    Function.Surjective (mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) f x) := by
  classical
  have hfx : f x ∈ h.codChart.source := h.mem_codChart_source
  have hxs : x ∈ h.domChart.source := h.mem_domChart_source
  -- `C x` lies in the interior of the target of the extended domain chart
  have hCint : (⇑(h.domChart.extend I)) x ∈ interior (h.domChart.extend I).target :=
    (isInteriorPoint_iff_of_mem_maximalAtlas (by simp) h.domChart_mem_maximalAtlas hxs).mp hx
  have hCtgt : (⇑(h.domChart.extend I)) x ∈ (h.domChart.extend I).target :=
    (h.domChart.extend I).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hxs)
  -- the normal form, at `x`: `h.equiv (C x) = (ψ (f x), ·)`
  have hux : h.equiv ((⇑(h.domChart.extend I)) x) =
      ((h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) (f x),
        (h.equiv ((⇑(h.domChart.extend I)) x)).2) := by
    refine Prod.ext ?_ rfl
    have h1 := h.writtenInCharts hCtgt
    simp only [Function.comp_apply] at h1
    rw [show (h.domChart.extend I).symm ((⇑(h.domChart.extend I)) x) = x from
      (h.domChart.extend I).left_inv (by
        rw [OpenPartialHomeomorph.extend_source]; exact hxs)] at h1
    simpa using h1.symm
  have hux' : h.equiv.symm
      ((h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) (f x),
        (h.equiv ((⇑(h.domChart.extend I)) x)).2) = (⇑(h.domChart.extend I)) x := by
    rw [← hux, ContinuousLinearEquiv.symm_apply_apply]
  -- the local section of `f` near `f x`
  let Φ : EuclideanSpace ℝ (Fin k) → E := fun y =>
    h.equiv.symm (y, (h.equiv ((⇑(h.domChart.extend I)) x)).2)
  let sec : EuclideanSpace ℝ (Fin k) → M := fun y =>
    (⇑(h.domChart.extend I).symm)
      (Φ ((h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) y))
  have hchart : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (⇑(h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))))) (f x) :=
    (OpenPartialHomeomorph.contMDiffAt_extend h.codChart_mem_maximalAtlas hfx).mdifferentiableAt
      (by simp)
  have hΦ : ∀ y, MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, E)
      Φ y := by
    intro y
    have h1 : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin k) × h.complement)
        (fun z : EuclideanSpace ℝ (Fin k) => (z, (0 : h.complement))) y :=
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k)) h.complement).mdifferentiableAt
    have h2 : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin k) × h.complement)
        (fun _ : EuclideanSpace ℝ (Fin k) =>
          ((0 : EuclideanSpace ℝ (Fin k)), (h.equiv ((⇑(h.domChart.extend I)) x)).2)) y :=
      mdifferentiableAt_const
    have h3 : (fun z : EuclideanSpace ℝ (Fin k) =>
          (z, (h.equiv ((⇑(h.domChart.extend I)) x)).2))
        = (fun z : EuclideanSpace ℝ (Fin k) => (z, (0 : h.complement)))
          + (fun _ : EuclideanSpace ℝ (Fin k) =>
              ((0 : EuclideanSpace ℝ (Fin k)), (h.equiv ((⇑(h.domChart.extend I)) x)).2)) := by
      funext z; simp
    have h4 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × h.complement) 𝓘(ℝ, E)
        (⇑h.equiv.symm)
        ((fun z : EuclideanSpace ℝ (Fin k) =>
          (z, (h.equiv ((⇑(h.domChart.extend I)) x)).2)) y) :=
      (h.equiv.symm : (EuclideanSpace ℝ (Fin k) × h.complement) →L[ℝ] E).mdifferentiableAt
    have h5 : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, E)
        (⇑h.equiv.symm ∘ fun z : EuclideanSpace ℝ (Fin k) =>
          (z, (h.equiv ((⇑(h.domChart.extend I)) x)).2)) y :=
      MDifferentiableAt.comp y h4 (by rw [h3]; exact h1.add h2)
    simpa only [Φ, Function.comp_def] using h5
  have hΦchart : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, E)
      (Φ ∘ ⇑(h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))))) (f x) :=
    MDifferentiableAt.comp (f x)
      (hΦ ((h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) (f x))) hchart
  have hCinv' : MDifferentiableAt 𝓘(ℝ, E) I (⇑(h.domChart.extend I).symm)
      ((⇑(h.domChart.extend I)) x) := by
    have hmem : (h.domChart.extend I).target ∈ 𝓝 ((⇑(h.domChart.extend I)) x) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hCint)
        (show interior (h.domChart.extend I).target ⊆ (h.domChart.extend I).target from
          interior_subset)
    have h1 : ContMDiffOn 𝓘(ℝ, E) I ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑(h.domChart.extend I).symm)
        (h.domChart.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target']
      exact contMDiffOn_extend_symm h.domChart_mem_maximalAtlas
    exact (h1.contMDiffAt hmem).mdifferentiableAt (by simp)
  have hCinv : MDifferentiableAt 𝓘(ℝ, E) I (⇑(h.domChart.extend I).symm)
      (Φ ((h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) (f x))) := by
    simpa only [Φ, hux'] using hCinv'
  have hsec : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) I sec (f x) := by
    have h := MDifferentiableAt.comp (f x) hCinv hΦchart
    simpa only [sec, Function.comp_def] using h
  have hsecx : sec (f x) = x := by
    simp only [sec, Φ]
    rw [hux']
    exact (h.domChart.extend I).left_inv (by
      rw [OpenPartialHomeomorph.extend_source]; exact hxs)
  -- `sec` really is a local section of `f`
  have hpre : (Φ ∘ ⇑(h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))))) ⁻¹'
      interior (h.domChart.extend I).target ∈ 𝓝 (f x) := by
    refine hΦchart.continuousAt.preimage_mem_nhds ?_
    rw [show (Φ ∘ ⇑(h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))))) (f x)
        = (⇑(h.domChart.extend I)) x from ?_]
    · exact isOpen_interior.mem_nhds hCint
    · simp only [Function.comp_apply, Φ]
      exact hux'
  have hfg : f ∘ sec =ᶠ[𝓝 (f x)] id := by
    filter_upwards [h.codChart.open_source.mem_nhds hfx, hpre] with y hy hy'
    have htgt : Φ ((h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) y)
        ∈ (h.domChart.extend I).target := interior_subset hy'
    have h1 := h.writtenInCharts htgt
    simp only [Function.comp_apply] at h1
    rw [h.equiv.apply_symm_apply] at h1
    have h3 : (h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) (f (sec y))
        = (h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) y := by
      simpa only [Φ] using h1
    have h4 : h.codChart (f (sec y)) = h.codChart y := by
      simpa [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, Function.comp_def]
        using h3
    have hsrc : sec y ∈ h.domChart.source := by
      have hmem : (⇑(h.domChart.extend I).symm)
          (Φ ((h.codChart.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))) y))
          ∈ h.domChart.source := by
        have h' := PartialEquiv.map_source (h.domChart.extend I).symm (by
          rw [PartialEquiv.symm_source]; exact htgt)
        rw [PartialEquiv.symm_target, OpenPartialHomeomorph.extend_source] at h'
        exact h'
      simpa only [sec] using hmem
    have hfsec : f (sec y) ∈ h.codChart.source := h.source_subset_preimage_source hsrc
    have h5 : f (sec y) = h.codChart.symm (h.codChart (f (sec y))) :=
      (h.codChart.left_inv hfsec).symm
    rw [h4, h.codChart.left_inv hy] at h5
    simpa using h5
  -- chain rule
  have hfmd : MDifferentiableAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) f x :=
    h.contMDiffAt.mdifferentiableAt (by simp)
  have hgsec : MDifferentiableAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) f
      (sec (f x)) := by
    rw [hsecx]; exact hfmd
  have hchain : (mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) f x).comp
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) I sec (f x)) =
      ContinuousLinearMap.id ℝ
        (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) (f x)) := by
    have h2 := mfderiv_comp (x := f x) (f := sec) (g := f) hgsec hsec
    have h1 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) (f ∘ sec) (f x) =
        ContinuousLinearMap.id ℝ
          (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) (f x)) := by
      rw [Filter.EventuallyEq.mfderiv_eq hfg, mfderiv_id]
      all_goals first | rfl | (ext v; rfl) | simp
    rw [h1] at h2
    rw [hsecx] at h2
    exact h2.symm
  -- conclude
  intro v
  refine ⟨(mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) I sec (f x)) v, ?_⟩
  have h := congrArg (fun L : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) (f x)
      →L[ℝ] TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) (f x) => L v) hchain
  rw [ContinuousLinearMap.id_apply] at h
  exact h

end

end Work.ThomBordism.Transversality.TransversalApproximation
