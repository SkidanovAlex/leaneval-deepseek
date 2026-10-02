import Mathlib
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.transversalApproximation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Surjective `mfderiv` at an interior point implies `IsSubmersionAt` (real-valued case)

Mathlib's `Manifold.IsSubmersionAt` is defined by a local normal form (in suitable charts `f` looks
like `(u, v) ↦ u`); the equivalence with surjectivity of `mfderiv` at an interior point is a TODO of
`Mathlib/Geometry/Manifold/Submersion.lean`.

For a target `EuclideanSpace ℝ (Fin k)` this was proved in
`Work.ThomBordism.Transversality.TransverseSard.isSubmersionAt_of_surjective_fderiv_localRep`
(the hard direction, via the inverse function theorem and a conjugation of the source chart by a
local diffeomorphism of the model space).  Here we deduce the case of a *real-valued* map
`f : M → ℝ` (with the model with corners `modelWithCornersSelf ℝ ℝ = 𝓘(ℝ,ℝ)` on the target),
which is what the PT-geometric development needs:

* `surjective_mfderiv_iff_surjective_fderiv_extChartAt_real` — the chart bridge identifying
  `mfderiv Idx 𝓘(ℝ,ℝ) f x` with the ordinary derivative of the chart expression of `f`.
* `isSubmersionAt_real_of_euclidOne` — transport of `IsSubmersionAt` from the target
  `EuclideanSpace ℝ (Fin 1)` to the target `ℝ`, by conjugating the codomain chart by the linear
  isometry equivalence `euclidOneEquiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1)`.
* `isSubmersionAt_of_surjective_mfderiv_real` — the main statement.

## Implementation notes

The transport `isSubmersionAt_real_of_euclidOne` unpacks the submersion datum for
`y ↦ euclidOneEquiv (f y)` (charts `domChart`, `codChart : ℝ¹ → ℝ¹`, a linear equivalence
`equiv : E ≃L ℝ¹ × F` with `codChart (euclidOneEquiv (f y)) = (equiv ((domChart.extend Idx) y)).1`) and
rebuilds the datum for `f`:

* new codomain chart `T := euclidOneEquiv ≫ₕ codChart ≫ₕ euclidOneEquiv.symm`, i.e. `T t = euclidOneEquiv.symm (codChart (euclidOneEquiv t))`
  (it lies in the maximal atlas of `𝓘(ℝ,ℝ)` because it and its inverse are `C^∞` on their sources);
* new linear equivalence `equiv' : E ≃L (ℝ × ker ℓ)` for `ℓ := euclidOneEquiv.symm ∘ fst ∘ equiv`, so that
  `fst ∘ equiv' = ℓ = euclidOneEquiv.symm ∘ fst ∘ equiv`.

Then `T (f y) = euclidOneEquiv.symm (codChart (euclidOneEquiv (f y))) = euclidOneEquiv.symm ((equiv z).1) = ℓ z`.
-/

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
-- needed for the `mfderiv`/`fderiv` bridge: `TangentSpace I x` is a `def`, so instance search
-- has to unfold it (cf. the same option in `TransversalApproximation/chartBridge.lean`).
set_option backward.isDefEq.respectTransparency false

/-- The linear isometry equivalence `ℝ ≃L[ℝ] ℝ¹` (`ℝ¹ = EuclideanSpace ℝ (Fin 1)`). -/
def euclidOneEquiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm).trans
    ((EuclideanSpace.equiv (Fin 1) ℝ).symm)

/-- **The chart bridge for a real-valued map.**

At an interior point `x`, surjectivity of `mfderiv Idx 𝓘(ℝ,ℝ) f x` is equivalent to surjectivity of
the ordinary derivative of the chart expression `z ↦ f ((extChartAt Idx x).symm z)` at
`z = (extChartAt Idx x) x`.  This is
`Work.ThomBordism.Transversality.TransversalApproximation.surjective_mfderiv_iff_surjective_fderiv_extChartAt`
with the target `𝓡 k` replaced by the model `𝓘(ℝ,ℝ)`. -/
theorem surjective_mfderiv_iff_surjective_fderiv_extChartAt_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] (Idx : ModelWithCorners ℝ E G) {M : Type*}
    [TopologicalSpace M] [ChartedSpace G M]
    [IsManifold Idx ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {x : M} (hx : Idx.IsInteriorPoint x)
    (hf : MDifferentiableAt Idx (modelWithCornersSelf ℝ ℝ) f x) :
    Function.Surjective (mfderiv Idx (modelWithCornersSelf ℝ ℝ) f x) ↔
      Function.Surjective
        (fderiv ℝ (fun z : E => f ((extChartAt Idx x).symm z)) ((extChartAt Idx x) x)) := by
  have hmem : (extChartAt Idx x) x ∈ interior (range Idx) := by
    rw [ModelWithCorners.isInteriorPoint_iff] at hx
    exact interior_mono (extChartAt_target_subset_range (I := Idx) x) hx
  have hnhds : range Idx ∈ 𝓝 ((extChartAt Idx x) x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hmem) interior_subset
  have hwritten : writtenInExtChartAt Idx (modelWithCornersSelf ℝ ℝ) x f =
      fun z : E => f ((extChartAt Idx x).symm z) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    rfl
  have h1 : HasFDerivWithinAt (fun z : E => f ((extChartAt Idx x).symm z))
      (mfderiv Idx (modelWithCornersSelf ℝ ℝ) f x) (range Idx) ((extChartAt Idx x) x) := by
    have h := hf.hasMFDerivAt
    unfold HasMFDerivAt at h
    rw [hwritten] at h
    exact h.2
  have h2 : fderiv ℝ (fun z : E => f ((extChartAt Idx x).symm z)) ((extChartAt Idx x) x) =
      mfderiv Idx (modelWithCornersSelf ℝ ℝ) f x := (h1.hasFDerivAt hnhds).fderiv
  rw [h2]
  rfl

/-- **Changing the target model of a submersion: `ℝ¹ ↦ ℝ`.**

If `y ↦ euclidOneEquiv (f y)` is a submersion at `x` into `EuclideanSpace ℝ (Fin 1)`, then `f` is a
submersion at `x` into `ℝ`. -/
theorem isSubmersionAt_real_of_euclidOne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] (Idx : ModelWithCorners ℝ E G) {M : Type*}
    [TopologicalSpace M] [ChartedSpace G M]
    {f : M → ℝ} {x : M} (hfc : ContinuousAt f x)
    (h : Manifold.IsSubmersionAt Idx (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => euclidOneEquiv (f y)) x) :
    Manifold.IsSubmersionAt Idx (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f x := by
  obtain ⟨F, hFadd, hFmod, hF⟩ := h
  letI : NormedAddCommGroup F := hFadd
  letI : NormedSpace ℝ F := hFmod
  -- the conjugated codomain chart `T t = euclidOneEquiv.symm (codChart (euclidOneEquiv t))`
  set T : OpenPartialHomeomorph ℝ ℝ :=
    euclidOneEquiv.toHomeomorph.toOpenPartialHomeomorph ≫ₕ hF.codChart ≫ₕ
      euclidOneEquiv.symm.toHomeomorph.toOpenPartialHomeomorph with hT
  have hTfun : (T : ℝ → ℝ) = fun t => euclidOneEquiv.symm (hF.codChart (euclidOneEquiv t)) := by
    funext t
    rw [hT, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph]
  have hTsrc : T.source = euclidOneEquiv ⁻¹' hF.codChart.source := by
    simp only [hT, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, Set.univ_inter, Set.preimage_univ,
      Set.inter_univ]
  have hTsymm : (T.symm : ℝ → ℝ) = fun u => euclidOneEquiv.symm (hF.codChart.symm (euclidOneEquiv u)) := by
    funext u
    rw [hT, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_symm_apply,
      Homeomorph.toOpenPartialHomeomorph_symm_apply]
    simp only [← ContinuousLinearEquiv.toHomeomorph_symm, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.coe_toHomeomorph]
  have hTtgt : T.target = euclidOneEquiv ⁻¹' hF.codChart.target := by
    simp only [hT, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, Homeomorph.toOpenPartialHomeomorph_symm_apply,
      ContinuousLinearEquiv.toHomeomorph_symm, Homeomorph.symm_symm,
      ContinuousLinearEquiv.coe_toHomeomorph, Set.univ_inter, Set.preimage_univ,
      Set.inter_univ]
  -- `T` lies in the maximal atlas of `𝓘(ℝ,ℝ)` on `ℝ`
  have hTmem : T ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ℝ := by
    rw [IsManifold.mem_maximalAtlas_iff]
    refine StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ ?_
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
    have hself := Work.ThomBordism.Transversality.TransverseSard.contDiffOn_mem_maximalAtlas_self (k := 1)
      (B := hF.codChart) hF.codChart_mem_maximalAtlas
    have hcod : ContDiffOn ℝ ∞
        (hF.codChart : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) hF.codChart.source :=
      hself.1
    have hcods : ContDiffOn ℝ ∞
        (hF.codChart.symm : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
        hF.codChart.target := hself.2
    have h1c : ContDiffOn ℝ ∞ (fun t : ℝ => hF.codChart (euclidOneEquiv t))
        (euclidOneEquiv ⁻¹' hF.codChart.source) :=
      ContDiffOn.comp (t := hF.codChart.source) hcod
        ((ContinuousLinearMap.contDiff
          (euclidOneEquiv : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))).contDiffOn)
        (fun t ht => ht)
    have h1c' : ContDiffOn ℝ ∞ (fun t : ℝ => euclidOneEquiv.symm (hF.codChart (euclidOneEquiv t)))
        (euclidOneEquiv ⁻¹' hF.codChart.source) :=
      ContDiffOn.comp (t := Set.univ)
        ((ContinuousLinearMap.contDiff
          (euclidOneEquiv.symm : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)).contDiffOn)
        h1c (fun t _ => Set.mem_univ _)
    have h2c : ContDiffOn ℝ ∞ (fun u : ℝ => hF.codChart.symm (euclidOneEquiv u))
        (euclidOneEquiv ⁻¹' hF.codChart.target) :=
      ContDiffOn.comp (t := hF.codChart.target) hcods
        ((ContinuousLinearMap.contDiff
          (euclidOneEquiv : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))).contDiffOn)
        (fun u hu => hu)
    have h2c' : ContDiffOn ℝ ∞ (fun u : ℝ => euclidOneEquiv.symm (hF.codChart.symm (euclidOneEquiv u)))
        (euclidOneEquiv ⁻¹' hF.codChart.target) :=
      ContDiffOn.comp (t := Set.univ)
        ((ContinuousLinearMap.contDiff
          (euclidOneEquiv.symm : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)).contDiffOn)
        h2c (fun u _ => Set.mem_univ _)
    constructor
    · simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
        Set.preimage_id_eq, Function.id_comp, Function.comp_id, Set.inter_univ, id_eq]
      rwa [hTfun, hTsrc]
    · simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
        Set.preimage_id_eq, Function.id_comp, Function.comp_id, Set.inter_univ, id_eq]
      rwa [hTsymm, hTtgt]
  -- the first coordinate functional of the Euclidean submersion datum
  set ℓ : E →L[ℝ] ℝ := (euclidOneEquiv.symm : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1)) F).comp
      (hF.equiv : E →L[ℝ] (EuclideanSpace ℝ (Fin 1) × F))) with hℓ
  have hℓsurj : Function.Surjective ℓ := by
    have h1 : Function.Surjective
        ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1)) F).comp
          (hF.equiv : E →L[ℝ] (EuclideanSpace ℝ (Fin 1) × F))) := by
      intro w
      exact ⟨hF.equiv.symm (w, 0), by simp⟩
    intro w
    obtain ⟨v, hv⟩ := h1 (euclidOneEquiv w)
    refine ⟨v, ?_⟩
    rw [hℓ]
    simp only [ContinuousLinearMap.comp_apply, hv]
    exact ContinuousLinearEquiv.symm_apply_apply euclidOneEquiv w
  obtain ⟨σ, hσ⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective ℓ
    (LinearMap.range_eq_top.mpr hℓsurj)
  have hσ' : ∀ y : ℝ, ℓ (σ y) = y := fun y => by
    have := congrArg (fun (g : ℝ →L[ℝ] ℝ) => g y) hσ
    simpa using this
  let φeq : E →ₗ[ℝ] (ℝ × ℓ.ker) :=
    { toFun := fun v => (ℓ v, ⟨v - σ (ℓ v), by
        show ℓ (v - σ (ℓ v)) = 0
        rw [map_sub, hσ', sub_self]⟩)
      map_add' := fun v w => by
        refine Prod.ext ?_ ?_
        · show ℓ (v + w) = ℓ v + ℓ w
          rw [map_add]
        · refine Subtype.ext ?_
          show (v + w) - σ (ℓ (v + w)) = (v - σ (ℓ v)) + (w - σ (ℓ w))
          rw [map_add, map_add]
          abel
      map_smul' := fun c v => by
        refine Prod.ext ?_ ?_
        · show ℓ (c • v) = c • ℓ v
          rw [map_smul]
        · refine Subtype.ext ?_
          show (c • v) - σ (ℓ (c • v)) = c • (v - σ (ℓ v))
          rw [map_smul, map_smul, smul_sub] }
  have hbij : Function.Bijective φeq := by
    constructor
    · intro v w hvw
      have h1 : ℓ v = ℓ w := congrArg (fun p => p.1) hvw
      have h2 : (v - σ (ℓ v)) = (w - σ (ℓ w)) := congrArg (fun p => (p.2 : E)) hvw
      calc v = σ (ℓ v) + (v - σ (ℓ v)) := by abel
        _ = σ (ℓ w) + (w - σ (ℓ w)) := by rw [h2, h1]
        _ = w := by abel
    · intro p
      obtain ⟨y, w⟩ := p
      refine ⟨σ y + w, ?_⟩
      refine Prod.ext ?_ ?_
      · show ℓ (σ y + w) = y
        rw [map_add, hσ']
        have hw : ℓ (w : E) = 0 := w.2
        rw [hw, add_zero]
      · refine Subtype.ext ?_
        show ((σ y + w : E) - σ (ℓ (σ y + (w : E)))) = (w : E)
        rw [map_add, hσ']
        have hw : ℓ (w : E) = 0 := w.2
        rw [hw, add_zero, add_sub_cancel_left]
  let equiv' : E ≃L[ℝ] (ℝ × ℓ.ker) :=
    (LinearEquiv.ofBijective φeq hbij).toContinuousLinearEquiv
  have hequiv'_pr : ∀ v : E, (equiv' v).1 = ℓ v := fun v => rfl
  -- the normal form for `f` in the charts `domChart` and `T`
  have hEqOn : EqOn ((T.extend (modelWithCornersSelf ℝ ℝ)) ∘ f ∘
      (hF.domChart.extend Idx).symm) (Prod.fst ∘ ⇑equiv') (hF.domChart.extend Idx).target := by
    intro v hv
    have h1 := hF.writtenInCharts hv
    simp only [Function.comp_apply] at h1
    rw [OpenPartialHomeomorph.extend_coe] at h1
    simp only [Function.comp_apply, modelWithCornersSelf_coe, id_eq] at h1
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
      id_eq]
    rw [hTfun]
    simp only [h1, hequiv'_pr, hℓ, ContinuousLinearMap.comp_apply]
    rfl
  have hfxT : f x ∈ T.source := by
    rw [hTsrc]
    simpa using hF.mem_codChart_source
  refine (Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt (F := ℓ.ker) hfc equiv'
    hF.domChart T hF.mem_domChart_source hfxT hF.domChart_mem_maximalAtlas hTmem hEqOn).isSubmersionAt

/-- **At an interior point, a surjective `mfderiv` makes a real-valued `C^∞` map a submersion.** -/
theorem isSubmersionAt_of_surjective_mfderiv_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] (Idx : ModelWithCorners ℝ E G) {M : Type*}
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold Idx ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} (hf : ContMDiff Idx (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {x : M} (hx : Idx.IsInteriorPoint x) (hfx : f x = 0)
    (hsurj : Function.Surjective (mfderiv Idx (modelWithCornersSelf ℝ ℝ) f x)) :
    Manifold.IsSubmersionAt Idx (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f x := by
  have he : chartAt G x ∈ IsManifold.maximalAtlas Idx ((⊤ : ℕ∞) : WithTop ℕ∞) M :=
    IsManifold.chart_mem_maximalAtlas (I := Idx) x
  have hxsrc : x ∈ (chartAt G x).source := mem_chart_source G x
  have hxi : x ∉ Idx.boundary M := (Idx.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx
  have hVx : ((chartAt G x).extend Idx) x ∈ interior (((chartAt G x).extend Idx).target) :=
    (ModelWithCorners.isInteriorPoint_iff (I := Idx) (x := x)).mp hx
  have hrep : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => f (((chartAt G x).extend Idx).symm v))
      (interior (((chartAt G x).extend Idx).target)) :=
    (Work.ThomBordism.Transversality.TransverseSard.contDiffOn_localRep_of (I := Idx) hf he).mono (by
      rw [OpenPartialHomeomorph.extend_target']
      exact interior_subset)
  have hrepE : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => euclidOneEquiv (f (((chartAt G x).extend Idx).symm v)))
      (interior (((chartAt G x).extend Idx).target)) :=
    ContDiffOn.comp (t := Set.univ)
      ((ContinuousLinearMap.contDiff
        (euclidOneEquiv : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))).contDiffOn)
      hrep (fun v _ => Set.mem_univ v)
  have hsurj' : Function.Surjective
      (fderiv ℝ (fun v : E => f (((chartAt G x).extend Idx).symm v))
        (((chartAt G x).extend Idx) x)) :=
    (surjective_mfderiv_iff_surjective_fderiv_extChartAt_real Idx hx
      ((hf x).mdifferentiableAt (by simp))).mp hsurj
  have hsurjE : Function.Surjective
      (fderiv ℝ (fun v : E => euclidOneEquiv (f (((chartAt G x).extend Idx).symm v)))
        (((chartAt G x).extend Idx) x)) := by
    have hdiff : DifferentiableAt ℝ
        (fun v : E => f (((chartAt G x).extend Idx).symm v)) (((chartAt G x).extend Idx) x) :=
      (hrep.contDiffAt (isOpen_interior.mem_nhds hVx)).differentiableAt (by simp)
    have hcomp : fderiv ℝ (fun v : E => euclidOneEquiv (f (((chartAt G x).extend Idx).symm v)))
        (((chartAt G x).extend Idx) x)
        = (euclidOneEquiv : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp
          (fderiv ℝ (fun v : E => f (((chartAt G x).extend Idx).symm v))
            (((chartAt G x).extend Idx) x)) :=
      ((ContinuousLinearMap.hasFDerivAt
        (euclidOneEquiv : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))).comp _
        hdiff.hasFDerivAt).fderiv
    rw [hcomp]
    intro w
    obtain ⟨v, hv⟩ := hsurj' (euclidOneEquiv.symm w)
    exact ⟨v, by
      simp only [ContinuousLinearMap.comp_apply, hv]
      exact ContinuousLinearEquiv.apply_symm_apply euclidOneEquiv w⟩
  have hfx' : (fun y : M => euclidOneEquiv (f y)) x = 0 := by
    simp only [hfx, map_zero]
  have hE : Manifold.IsSubmersionAt Idx (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => euclidOneEquiv (f y)) x :=
    Work.ThomBordism.Transversality.TransverseSard.isSubmersionAt_of_surjective_fderiv_localRep (k := 1) (I := Idx)
      (e := chartAt G x) he hxsrc hxi hfx' isOpen_interior hVx interior_subset hrepE hsurjE
  exact isSubmersionAt_real_of_euclidOne Idx ((hf x).continuousAt) hE

end

end Work.PTGeometric
