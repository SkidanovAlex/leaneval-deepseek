import Mathlib
import Submission.Work.Projection.Defs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

variable {n k : ℕ}

/-- `(2 : ℕ∞ω) ≤ ∞`. -/
private lemma two_le_infty : (2 : ℕ∞ω) ≤ ∞ := by
  show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- The chart representation of `f` at `p` is smooth on the target of the chart at `p`. -/
lemma contDiffOn_chartRep {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p : M) :
    ContDiffOn ℝ ∞ (chartRep f p) (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
  have h : ContMDiffOn (𝓡 n) (𝓡 (k + 1)) ∞ (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (hf.contMDiffOn (s := Set.univ)).comp (contMDiffOn_chart_symm (x := p))
      (by intro x hx; trivial)
  exact h.contDiffOn

/-- The map `(y, w) ↦ (fderiv ℝ (chartRep f p) y) w` is `C^1` on
`(chartAt p).target × univ`. -/
lemma contDiffOn_fderivApply_chartRep {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p : M) :
    ContDiffOn ℝ 1 (fun yw : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (chartRep f p) yw.1) yw.2)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).target ×ˢ Set.univ) := by
  have h2 : ContDiffOn ℝ 2 (chartRep f p) (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (contDiffOn_chartRep f hf p).of_le two_le_infty
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ (chartRep f p))
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    h2.fderiv_of_isOpen (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target (by norm_num)
  exact (hfd.comp contDiffOn_fst (fun x hx => hx.1)).clm_apply contDiffOn_snd

/-- `extract` is `C^1` on the open set where the last coordinate does not vanish. -/
lemma contDiffOn_extract :
    ContDiffOn ℝ 1 (extract (k := k))
      {z : EuclideanSpace ℝ (Fin (k+1)) | z (Fin.last k) ≠ 0} := by
  have h : ContDiffOn ℝ 1 (fun z : EuclideanSpace ℝ (Fin (k+1)) => fun i : Fin k =>
      z (Fin.castSucc i) / z (Fin.last k))
      {z : EuclideanSpace ℝ (Fin (k+1)) | z (Fin.last k) ≠ 0} := by
    rw [contDiffOn_pi]
    intro i
    exact ContDiffOn.div
      (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (k+1)) (Fin.castSucc i)) :
        EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] ℝ).contDiff.contDiffOn)
      (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (k+1)) (Fin.last k)) :
        EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] ℝ).contDiff.contDiffOn)
      (fun z hz => hz)
  refine (EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.comp_contDiffOn h |>.congr ?_
  intro z _
  rfl

/-- The domain of the parametrisation of the immersion-bad directions of a single chart is
open. -/
lemma isOpen_immDom {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p : M) :
    IsOpen (immDom (n := n) (k := k) f p) := by
  have hcont : ContinuousOn
      (fun yw : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (chartRep f p) yw.1) yw.2)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).target ×ˢ Set.univ) :=
    (contDiffOn_fderivApply_chartRep (n := n) (k := k) f hf p).continuousOn
  have hset : immDom (n := n) (k := k) f p =
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).target ×ˢ Set.univ) ∩
        (fun yw : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ (chartRep f p) yw.1) yw.2) ⁻¹'
          {c : EuclideanSpace ℝ (Fin (k+1)) | c (Fin.last k) ≠ 0} := by
    ext yw
    simp only [immDom, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
      and_true, Set.mem_preimage]
  rw [hset]
  refine hcont.isOpen_inter_preimage
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.prod isOpen_univ) ?_
  exact isOpen_ne.preimage
    (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (k+1)) (Fin.last k)) :
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] ℝ).continuous)

/-- The parametrisation of the immersion-bad directions of a single chart is `C^1` on its
domain. -/
lemma contDiffOn_immParam {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p : M) :
    ContDiffOn ℝ 1 (immParam (n := n) (k := k) f p) (immDom (n := n) (k := k) f p) := by
  have hH : ContDiffOn ℝ 1
      (fun yw : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (chartRep f p) yw.1) yw.2) (immDom (n := n) (k := k) f p) :=
    (contDiffOn_fderivApply_chartRep (n := n) (k := k) f hf p).mono fun yw hyw => ⟨hyw.1, trivial⟩
  exact (contDiffOn_extract (k := k)).comp hH fun yw hyw => hyw.2

/-- Every immersion-bad direction occurs as the value of the parametrisation of the bad set of
one of the charts. -/
lemma badImmCharts_subset {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (_ : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (p : ℕ → M) :
    badImmCharts (n := n) (k := k) f p ⊆
      ⋃ i, immParam (n := n) (k := k) f (p i) '' (immDom (n := n) (k := k) f (p i)) := by
  rintro u ⟨i, y, hy, w, hw⟩
  refine Set.mem_iUnion.2 ⟨i, ⟨(y, w), ⟨hy, ?_⟩, ?_⟩⟩
  · rw [hw, vVec_last]
    norm_num
  · simp only [immParam]
    rw [hw, extract_vVec]

/-- The set of "immersion-bad" projection directions (parametrised by `u : ℝ^k`, the direction
of the kernel being spanned by `(u,1)`) has Hausdorff dimension at most `2*n`. -/
theorem dimH_badImmCharts {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (p : ℕ → M) : dimH (Work.Projection.badImmCharts (n := n) (k := k) f p) ≤ 2 * n := by
  calc dimH (badImmCharts (n := n) (k := k) f p)
      ≤ dimH (⋃ i, immParam (n := n) (k := k) f (p i) '' (immDom (n := n) (k := k) f (p i))) :=
        dimH_mono (badImmCharts_subset (n := n) (k := k) f hf p)
    _ = ⨆ i, dimH (immParam (n := n) (k := k) f (p i) '' (immDom (n := n) (k := k) f (p i))) := dimH_iUnion _
    _ ≤ 2 * n := by
      refine iSup_le fun i => ?_
      calc dimH (immParam (n := n) (k := k) f (p i) '' (immDom (n := n) (k := k) f (p i)))
          ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
            dimH_image_le_of_contDiffOn (isOpen_immDom (n := n) (k := k) f hf (p i))
              (contDiffOn_immParam (n := n) (k := k) f hf (p i)) (Set.Subset.refl _)
        _ = 2 * n := by
            rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
            push_cast
            ring

end Work.Projection
