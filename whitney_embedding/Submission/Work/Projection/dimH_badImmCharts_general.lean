import Mathlib
import Submission.Work.Projection.GeneralDefs
import Submission.Work.Projection.dimH_badImmCharts
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

namespace Work.Projection

open scoped Manifold ContDiff ENNReal
open Topology MeasureTheory

/-!
# The Hausdorff dimension of the immersion-bad directions for a general model with corners

`Submission/Work/Projection/GeneralDefs.lean` defines, for a smooth map `f` on a manifold modelled
on an arbitrary model with corners `I : ModelWithCorners ℝ E H`, the chartwise immersion-bad set
`badImmChartsI f p` using the *extended* charts `extChartAt I p : M → E`.

The present file bounds its Hausdorff dimension by `2 * finrank ℝ E`, mirroring the Euclidean
development of `dimH_badImmCharts.lean` (which is the case `E = EuclideanSpace ℝ (Fin n)`).
The parametrising maps live on `E × E`, so the bound is `finrank ℝ (E × E) = 2 * finrank ℝ E`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- `(2 : ℕ∞ω) ≤ ∞`. -/
private lemma two_le_infty_gen : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- The representation `y ↦ f (extChart⁻¹ y)` of `f` in the extended chart at `p` is smooth on
the target of that extended chart. -/
lemma contDiffOn_chartRepI {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p : M) :
    ContDiffOn ℝ ∞ (chartRepI (I := I) f p) (extChartAt I p).target := by
  have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞
      (chartRepI (I := I) f p) (extChartAt I p).target :=
    (hf.contMDiffOn (s := Set.univ)).comp
      (contMDiffOn_extChartAt_symm (I := I) p) (by intro x hx; trivial)
  exact h.contDiffOn

/-- The map `(y, w) ↦ (fderiv ℝ (chartRepI f p) y) w` is `C^1` on
`(extChartAt I p).target × univ`. -/
lemma contDiffOn_fderivApply_chartRepI {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless] {k : ℕ}
    (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p : M) :
    ContDiffOn ℝ 1 (fun yw : E × E => (fderiv ℝ (chartRepI (I := I) f p) yw.1) yw.2)
      ((extChartAt I p).target ×ˢ Set.univ) := by
  have h2 : ContDiffOn ℝ 2 (chartRepI (I := I) f p) (extChartAt I p).target :=
    (contDiffOn_chartRepI (I := I) f hf p).of_le two_le_infty_gen
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ (chartRepI (I := I) f p)) (extChartAt I p).target :=
    h2.fderiv_of_isOpen (isOpen_extChartAt_target (I := I) p) (by norm_num)
  exact (hfd.comp contDiffOn_fst (fun x hx => hx.1)).clm_apply contDiffOn_snd

/-- The domain of the parametrisation of the immersion-bad set of the extended chart at `p` is
open. -/
lemma isOpen_immDomI {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p : M) :
    IsOpen (immDomI (I := I) f p) := by
  have hcont : ContinuousOn
      (fun yw : E × E => (fderiv ℝ (chartRepI (I := I) f p) yw.1) yw.2)
      ((extChartAt I p).target ×ˢ Set.univ) :=
    (contDiffOn_fderivApply_chartRepI (I := I) f hf p).continuousOn
  have hset : immDomI (I := I) f p =
      ((extChartAt I p).target ×ˢ Set.univ) ∩
        (fun yw : E × E => (fderiv ℝ (chartRepI (I := I) f p) yw.1) yw.2) ⁻¹'
          {c : EuclideanSpace ℝ (Fin (k+1)) | c (Fin.last k) ≠ 0} := by
    ext yw
    simp only [immDomI, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
      and_true, Set.mem_preimage, fderivWithin_range_I]
  rw [hset]
  refine hcont.isOpen_inter_preimage ?_ ?_
  · exact (isOpen_extChartAt_target (I := I) p).prod isOpen_univ
  · exact isOpen_ne.preimage
      (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (k+1)) (Fin.last k)) :
        EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] ℝ).continuous)

/-- The parametrisation of the immersion-bad set of the extended chart at `p` is `C^1` on its
domain. -/
lemma contDiffOn_immParamI {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p : M) :
    ContDiffOn ℝ 1 (immParamI (I := I) f p) (immDomI (I := I) f p) := by
  have hH : ContDiffOn ℝ 1
      (fun yw : E × E => (fderiv ℝ (chartRepI (I := I) f p) yw.1) yw.2)
      (immDomI (I := I) f p) :=
    (contDiffOn_fderivApply_chartRepI (I := I) f hf p).mono (fun yw hyw => ⟨hyw.1, trivial⟩)
  have hg : ContDiffOn ℝ 1
      (fun yw : E × E => extract ((fderiv ℝ (chartRepI (I := I) f p) yw.1) yw.2))
      (immDomI (I := I) f p) := by
    refine (contDiffOn_extract (k := k)).comp hH ?_
    intro yw hyw
    simpa only [Set.mem_ofPred_eq, fderivWithin_range_I] using hyw.2
  refine hg.congr ?_
  intro yw hyw
  simp only [immParamI, fderivWithin_range_I]

/-- The set of immersion-bad projection directions of a smooth map from a manifold modelled on `E`
has Hausdorff dimension at most `2 * finrank ℝ E`. -/
theorem dimH_badImmCharts_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p : ℕ → M) :
    dimH (Work.Projection.badImmChartsI (I := I) f p) ≤ (2 * Module.finrank ℝ E : ℕ) := by
  calc dimH (Work.Projection.badImmChartsI (I := I) f p)
      ≤ dimH (⋃ i, immParamI (I := I) f (p i) '' (immDomI (I := I) f (p i))) :=
        dimH_mono (badImmChartsI_subset (I := I) f p)
    _ = ⨆ i, dimH (immParamI (I := I) f (p i) '' (immDomI (I := I) f (p i))) :=
        dimH_iUnion _
    _ ≤ (2 * Module.finrank ℝ E : ℕ) := by
      refine iSup_le fun i => ?_
      have h := dimH_image_le_of_contDiffOn (isOpen_immDomI (I := I) f hf (p i))
        (contDiffOn_immParamI (I := I) f hf (p i)) (Set.Subset.refl _)
      have hfin : (Module.finrank ℝ (E × E) : ℝ≥0∞) =
          ((2 * Module.finrank ℝ E : ℕ) : ℝ≥0∞) := by
        rw [Module.finrank_prod]
        push_cast
        ring
      rwa [hfin] at h

end Work.Projection
