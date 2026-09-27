import Mathlib
import Submission.Work.Projection.Defs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

section Helpers

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The chart representation of a `C^∞` map is `C^∞` on the target of the chart. -/
lemma chartRep_contDiffOn (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p : M) :
    ContDiffOn ℝ ∞ (chartRep f p) (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
  have h : ContMDiffOn (𝓡 n) (𝓡 (k+1)) ∞
      (fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    ContMDiffOn.comp (t := (Set.univ : Set M))
      hf.contMDiffOn (contMDiffOn_chart_symm (x := p)) (Set.subset_univ _)
  exact h.contDiffOn

/-- `extract` is `C^∞` on the open set where the last coordinate does not vanish. -/
lemma contDiffOn_extract_inj (k : ℕ) : ContDiffOn ℝ ∞ (extract (k := k))
      {z : EuclideanSpace ℝ (Fin (k+1)) | z (Fin.last k) ≠ 0} := by
  have hF : ContDiffOn ℝ ∞
      (fun w : Fin (k+1) → ℝ => fun i : Fin k => w (Fin.castSucc i) / w (Fin.last k))
      {w : Fin (k+1) → ℝ | w (Fin.last k) ≠ 0} := by
    rw [contDiffOn_pi]
    intro i
    exact (ContinuousLinearMap.contDiff
        (ContinuousLinearMap.proj (Fin.castSucc i) : (Fin (k+1) → ℝ) →L[ℝ] ℝ)).contDiffOn.div
      (ContinuousLinearMap.contDiff
        (ContinuousLinearMap.proj (Fin.last k) : (Fin (k+1) → ℝ) →L[ℝ] ℝ)).contDiffOn
      (fun w hw => hw)
  have hcomp : ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin (k+1)) =>
        (EuclideanSpace.equiv (Fin k) ℝ).symm
          ((fun w : Fin (k+1) → ℝ => fun i : Fin k => w (Fin.castSucc i) / w (Fin.last k))
            ((EuclideanSpace.equiv (Fin (k+1)) ℝ) z)))
      {z : EuclideanSpace ℝ (Fin (k+1)) | z (Fin.last k) ≠ 0} := by
    refine ContDiffOn.comp
      (f := fun z => (fun w : Fin (k+1) → ℝ => fun i : Fin k => w (Fin.castSucc i) / w (Fin.last k))
            ((EuclideanSpace.equiv (Fin (k+1)) ℝ) z))
      (t := Set.univ)
      ((ContinuousLinearEquiv.contDiff (EuclideanSpace.equiv (Fin k) ℝ).symm).contDiffOn)
      ?_ ?_
    · exact hF.comp
        ((ContinuousLinearEquiv.contDiff (EuclideanSpace.equiv (Fin (k+1)) ℝ)).contDiffOn)
        (fun z hz => hz)
    · intro z hz; trivial
  exact hcomp

/-- The difference of the two chart representatives of `f` is `C^∞` on the product of the
two chart targets. -/
lemma contDiffOn_diff (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p q : M) :
    ContDiffOn ℝ ∞ (fun yz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        chartRep f p yz.1 - chartRep f q yz.2)
      {yz | yz.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
            yz.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target} := by
  refine ((chartRep_contDiffOn (n := n) f hf p).comp contDiff_fst.contDiffOn ?_).sub
    ((chartRep_contDiffOn (n := n) f hf q).comp contDiff_snd.contDiffOn ?_)
  · intro yz hyz; exact hyz.1
  · intro yz hyz; exact hyz.2

/-- The domain of the injectivity-bad parametrisation is open. -/
lemma isOpen_injDom (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p q : M) :
    IsOpen (injDom (n := n) (k := k) f p q) := by
  set T : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {yz | yz.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
          yz.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target} with hT
  have hTop : IsOpen T := by
    rw [hT]
    exact ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.preimage continuous_fst).inter
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).open_target.preimage continuous_snd)
  have hcont : ContinuousOn (fun yz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (chartRep f p yz.1 - chartRep f q yz.2) (Fin.last k)) T :=
    (by fun_prop : Continuous (fun z : EuclideanSpace ℝ (Fin (k+1)) => z (Fin.last k))).comp_continuousOn
      (contDiffOn_diff (n := n) f hf p q).continuousOn
  have h := hcont.isOpen_inter_preimage hTop (isOpen_compl_singleton (x := (0 : ℝ)))
  have heq : injDom (n := n) (k := k) f p q
      = T ∩ (fun yz => (chartRep f p yz.1 - chartRep f q yz.2) (Fin.last k)) ⁻¹' ({0} : Set ℝ)ᶜ := by
    ext yz; simp [injDom, hT, Set.mem_compl_iff]; tauto
  rw [heq]; exact h

/-- The injectivity-bad parametrisation is `C^1` on its domain. -/
lemma contDiffOn_injParam (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f) (p q : M) :
    ContDiffOn ℝ 1 (injParam (n := n) (k := k) f p q) (injDom (n := n) (k := k) f p q) := by
  have hdiff : ContDiffOn ℝ ∞
      (fun yz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        chartRep f p yz.1 - chartRep f q yz.2)
      (injDom (n := n) (k := k) f p q) :=
    (contDiffOn_diff (n := n) f hf p q).mono (fun yz hyz => ⟨hyz.1, hyz.2.1⟩)
  have hcomp : ContDiffOn ℝ ∞ (injParam (n := n) (k := k) f p q)
      (injDom (n := n) (k := k) f p q) :=
    (contDiffOn_extract_inj k).comp hdiff (fun yz hyz => hyz.2.2)
  exact hcomp.of_le (by simp)

end Helpers

/-- The set of "injectivity-bad" projection directions (parametrised by `u : ℝ^k`, the direction
of the kernel being spanned by `(u,1)`) has Hausdorff dimension at most `2*n`. -/
theorem dimH_badInjCharts {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (p : ℕ → M) : dimH (Work.Projection.badInjCharts (n := n) (k := k) f p) ≤ 2 * n := by
  have hsub : badInjCharts (n := n) (k := k) f p ⊆
      ⋃ i, ⋃ j, injParam (n := n) (k := k) f (p i) (p j) '' injDom (n := n) (k := k) f (p i) (p j) := by
    rintro u ⟨i, j, y, hy, z, hz, hlast, hext⟩
    refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    exact ⟨(y, z), ⟨hy, hz, hlast⟩, hext⟩
  calc dimH (badInjCharts (n := n) (k := k) f p)
      ≤ dimH (⋃ i, ⋃ j, injParam (n := n) (k := k) f (p i) (p j) '' injDom (n := n) (k := k) f (p i) (p j)) :=
          dimH_mono hsub
    _ = ⨆ i, ⨆ j, dimH (injParam (n := n) (k := k) f (p i) (p j) '' injDom (n := n) (k := k) f (p i) (p j)) := by
          simp only [dimH_iUnion]
    _ ≤ 2 * n := by
          refine iSup_le fun i => iSup_le fun j => ?_
          have h := dimH_image_le_of_contDiffOn (isOpen_injDom (n := n) f hf (p i) (p j))
            (contDiffOn_injParam (n := n) f hf (p i) (p j)) (Set.Subset.rfl)
          have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))  : ENNReal)
              = (2 * n : ENNReal) := by
            rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
            push_cast
            ring
          rwa [hfin] at h

end Work.Projection
