import Mathlib
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt
import Submission.Work.PTGeometric.isSubmersionAt_of_surjective_mfderiv_real

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Surjectivity of `mfderiv` for real-valued submersions at interior points

Mathlib's `Manifold.IsSubmersionAt` is defined by a local normal form (in suitable charts, `f`
looks like `(u, v) ↦ u`).  Its relation to surjectivity of `mfderiv` is an explicit TODO of
`Mathlib/Geometry/Manifold/Submersion.lean`.  Here we prove the direction needed by the
PT-geometric development, for a *real-valued* map `f : M → ℝ`:

`I.IsInteriorPoint x → IsSubmersionAt I 𝓘(ℝ,ℝ) f x → Surjective (mfderiv I 𝓘(ℝ,ℝ) f x)`.

This is the same proof as
`Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt`
(the case of the target `EuclideanSpace ℝ (Fin k)`), with `EuclideanSpace ℝ (Fin k)` replaced by
`ℝ`; nothing in that proof uses a special feature of `Fin k`.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.PTGeometric

noncomputable section

/-- **At an interior point, a `C^∞` submersion `f : M → ℝ` into `ℝ` has surjective `mfderiv`.**

Mathlib's `Manifold.IsSubmersionAt` is the local-normal-form notion (charts in which `f` looks like
`(u, v) ↦ u`); its equivalence with surjectivity of `mfderiv` is an explicit TODO of
`Mathlib/Geometry/Manifold/Submersion.lean` and is not in the library.

For the target `EuclideanSpace ℝ (Fin k)` with model `𝓡 k` the same result is already proved in this
workspace, as
`Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt`: its
proof constructs a local section `sec` of `f` out of the normal-form data of
`h : IsSubmersionAt` and concludes `mfderiv f x ∘ mfderiv sec (f x) = id` from the chain rule.  It
uses no special feature of `Fin k`, so the present claim is the same result with
`EuclideanSpace ℝ (Fin k)` replaced by `ℝ` and `𝓡 k` replaced by `modelWithCornersSelf ℝ ℝ`; a
verbatim adaptation of that proof is the intended route.  The mathematical inputs are only:
`h.domChart.extend I` has invertible derivative, `h.equiv.symm` is linear, and
`h.codChart.extend 𝓘(ℝ,ℝ)` is a local diffeomorphism at `f x`.

An alternative route: transport the submersion datum along the linear isometry equivalence
`euclidOneEquiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1)` (defined in
`Submission/Work/PTGeometric/isSubmersionAt_of_surjective_mfderiv_real.lean`, whose
`isSubmersionAt_real_of_euclidOne` performs the transportation in the *opposite* direction), apply
the `Fin k` version with `k = 1`, and finish with `mfderiv_comp` and the bijectivity of
`euclidOneEquiv`.

The claim is mathematically true. -/
theorem mfderiv_surjective_of_isSubmersionAt_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {x : M} (hx : I.IsInteriorPoint x)
    (h : Manifold.IsSubmersionAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f x) :
    Function.Surjective (mfderiv I (modelWithCornersSelf ℝ ℝ) f x) := by
  classical
  have hfx : f x ∈ h.codChart.source := h.mem_codChart_source
  have hxs : x ∈ h.domChart.source := h.mem_domChart_source
  -- `C x` lies in the interior of the target of the extended domain chart
  have hCint : (⇑(h.domChart.extend I)) x ∈ interior (h.domChart.extend I).target :=
    (Work.ThomBordism.Transversality.TransversalApproximation.isInteriorPoint_iff_of_mem_maximalAtlas (by simp) h.domChart_mem_maximalAtlas hxs).mp hx
  have hCtgt : (⇑(h.domChart.extend I)) x ∈ (h.domChart.extend I).target :=
    (h.domChart.extend I).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hxs)
  -- the normal form, at `x`: `h.equiv (C x) = (ψ (f x), ·)`
  have hux : h.equiv ((⇑(h.domChart.extend I)) x) =
      ((h.codChart.extend (modelWithCornersSelf ℝ ℝ)) (f x),
        (h.equiv ((⇑(h.domChart.extend I)) x)).2) := by
    refine Prod.ext ?_ rfl
    have h1 := h.writtenInCharts hCtgt
    simp only [Function.comp_apply] at h1
    rw [show (h.domChart.extend I).symm ((⇑(h.domChart.extend I)) x) = x from
      (h.domChart.extend I).left_inv (by
        rw [OpenPartialHomeomorph.extend_source]; exact hxs)] at h1
    simpa using h1.symm
  have hux' : h.equiv.symm
      ((h.codChart.extend (modelWithCornersSelf ℝ ℝ)) (f x),
        (h.equiv ((⇑(h.domChart.extend I)) x)).2) = (⇑(h.domChart.extend I)) x := by
    rw [← hux, ContinuousLinearEquiv.symm_apply_apply]
  -- the local section of `f` near `f x`
  let Φ : ℝ → E := fun y =>
    h.equiv.symm (y, (h.equiv ((⇑(h.domChart.extend I)) x)).2)
  let sec : ℝ → M := fun y =>
    (⇑(h.domChart.extend I).symm)
      (Φ ((h.codChart.extend (modelWithCornersSelf ℝ ℝ)) y))
  have hchart : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ)
      (⇑(h.codChart.extend (modelWithCornersSelf ℝ ℝ))) (f x) :=
    (OpenPartialHomeomorph.contMDiffAt_extend h.codChart_mem_maximalAtlas hfx).mdifferentiableAt
      (by simp)
  have hΦ : ∀ y, MDifferentiableAt (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, E)
      Φ y := by
    intro y
    have h1 : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
        𝓘(ℝ, ℝ × h.complement)
        (fun z : ℝ => (z, (0 : h.complement))) y :=
      (ContinuousLinearMap.inl ℝ ℝ h.complement).mdifferentiableAt
    have h2 : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
        𝓘(ℝ, ℝ × h.complement)
        (fun _ : ℝ =>
          ((0 : ℝ), (h.equiv ((⇑(h.domChart.extend I)) x)).2)) y :=
      mdifferentiableAt_const
    have h3 : (fun z : ℝ =>
          (z, (h.equiv ((⇑(h.domChart.extend I)) x)).2))
        = (fun z : ℝ => (z, (0 : h.complement)))
          + (fun _ : ℝ =>
              ((0 : ℝ), (h.equiv ((⇑(h.domChart.extend I)) x)).2)) := by
      funext z; simp
    have h4 : MDifferentiableAt 𝓘(ℝ, ℝ × h.complement) 𝓘(ℝ, E)
        (⇑h.equiv.symm)
        ((fun z : ℝ =>
          (z, (h.equiv ((⇑(h.domChart.extend I)) x)).2)) y) :=
      (h.equiv.symm : (ℝ × h.complement) →L[ℝ] E).mdifferentiableAt
    have h5 : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, E)
        (⇑h.equiv.symm ∘ fun z : ℝ =>
          (z, (h.equiv ((⇑(h.domChart.extend I)) x)).2)) y :=
      MDifferentiableAt.comp y h4 (by rw [h3]; exact h1.add h2)
    simpa only [Φ, Function.comp_def] using h5
  have hΦchart : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, E)
      (Φ ∘ ⇑(h.codChart.extend (modelWithCornersSelf ℝ ℝ))) (f x) :=
    MDifferentiableAt.comp (f x)
      (hΦ ((h.codChart.extend (modelWithCornersSelf ℝ ℝ)) (f x))) hchart
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
      (Φ ((h.codChart.extend (modelWithCornersSelf ℝ ℝ)) (f x))) := by
    simpa only [Φ, hux'] using hCinv'
  have hsec : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I sec (f x) := by
    have h := MDifferentiableAt.comp (f x) hCinv hΦchart
    simpa only [sec, Function.comp_def] using h
  have hsecx : sec (f x) = x := by
    simp only [sec, Φ]
    rw [hux']
    exact (h.domChart.extend I).left_inv (by
      rw [OpenPartialHomeomorph.extend_source]; exact hxs)
  -- `sec` really is a local section of `f`
  have hpre : (Φ ∘ ⇑(h.codChart.extend (modelWithCornersSelf ℝ ℝ))) ⁻¹'
      interior (h.domChart.extend I).target ∈ 𝓝 (f x) := by
    refine hΦchart.continuousAt.preimage_mem_nhds ?_
    rw [show (Φ ∘ ⇑(h.codChart.extend (modelWithCornersSelf ℝ ℝ))) (f x)
        = (⇑(h.domChart.extend I)) x from ?_]
    · exact isOpen_interior.mem_nhds hCint
    · simp only [Function.comp_apply, Φ]
      exact hux'
  have hfg : f ∘ sec =ᶠ[𝓝 (f x)] id := by
    filter_upwards [h.codChart.open_source.mem_nhds hfx, hpre] with y hy hy'
    have htgt : Φ ((h.codChart.extend (modelWithCornersSelf ℝ ℝ)) y)
        ∈ (h.domChart.extend I).target := interior_subset hy'
    have h1 := h.writtenInCharts htgt
    simp only [Function.comp_apply] at h1
    rw [h.equiv.apply_symm_apply] at h1
    have h3 : (h.codChart.extend (modelWithCornersSelf ℝ ℝ)) (f (sec y))
        = (h.codChart.extend (modelWithCornersSelf ℝ ℝ)) y := by
      simpa only [Φ] using h1
    have h4 : h.codChart (f (sec y)) = h.codChart y := by
      simpa [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, Function.comp_def]
        using h3
    have hsrc : sec y ∈ h.domChart.source := by
      have hmem : (⇑(h.domChart.extend I).symm)
          (Φ ((h.codChart.extend (modelWithCornersSelf ℝ ℝ)) y))
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
  have hfmd : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f x :=
    h.contMDiffAt.mdifferentiableAt (by simp)
  have hgsec : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f
      (sec (f x)) := by
    rw [hsecx]; exact hfmd
  have hchain : (mfderiv I (modelWithCornersSelf ℝ ℝ) f x).comp
      (mfderiv (modelWithCornersSelf ℝ ℝ) I sec (f x)) =
      ContinuousLinearMap.id ℝ
        (TangentSpace (modelWithCornersSelf ℝ ℝ) (f x)) := by
    have h2 := mfderiv_comp (x := f x) (f := sec) (g := f) hgsec hsec
    have h1 : mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) (f ∘ sec) (f x) =
        ContinuousLinearMap.id ℝ
          (TangentSpace (modelWithCornersSelf ℝ ℝ) (f x)) := by
      rw [Filter.EventuallyEq.mfderiv_eq hfg, mfderiv_id]
      all_goals first | rfl | (ext v; rfl) | simp
    rw [h1] at h2
    rw [hsecx] at h2
    exact h2.symm
  -- conclude
  intro v
  refine ⟨(mfderiv (modelWithCornersSelf ℝ ℝ) I sec (f x)) v, ?_⟩
  have h := congrArg (fun L : TangentSpace (modelWithCornersSelf ℝ ℝ) (f x)
      →L[ℝ] TangentSpace (modelWithCornersSelf ℝ ℝ) (f x) => L v) hchain
  rw [ContinuousLinearMap.id_apply] at h
  exact h

end

end Work.PTGeometric
