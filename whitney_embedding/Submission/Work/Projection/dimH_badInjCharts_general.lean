import Mathlib
import Submission.Work.Projection.GeneralDefs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.dimH_badInjCharts

/-!
# The dimension of the injectivity-bad directions for a general model with corners

This file proves `dimH_badInjCharts_general`: for a smooth map `f : M → ℝ^{k+1}` on a manifold
modelled on a boundaryless model with corners `I : ModelWithCorners ℝ E H`, the set of
"injectivity-bad" projection directions (defined chartwise with the extended charts, see
`Submission/Work/Projection/GeneralDefs.lean`) has Hausdorff dimension at most `2 * finrank ℝ E`.

The proof is the same as for the standard model: the bad set is contained in a countable union of
images of the explicit parametrisations `injParamI f (p i) (p j)`, which are `C¹` on the open sets
`injDomI f (p i) (p j) ⊆ E × E`, and `dimH_image_le_of_contDiffOn` bounds the dimension of each
image by `finrank ℝ (E × E) = 2 * finrank ℝ E`.
-/

open scoped Manifold ContDiff
open Topology MeasureTheory

namespace Work.Projection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Helpers

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
/-- The extended-chart representation of a `C^∞` map is `C^∞` on the target of the extended
chart. -/
lemma contDiffOn_chartRepI {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p : M) :
    ContDiffOn ℝ ∞ (chartRepI (I := I) f p) (extChartAt I p).target := by
  have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞
      (fun y => f ((extChartAt I p).symm y)) (extChartAt I p).target :=
    ContMDiffOn.comp (t := Set.univ) hf.contMDiffOn (contMDiffOn_extChartAt_symm (I := I) p)
      (Set.subset_univ _)
  exact h.contDiffOn

omit [I.Boundaryless] in
/-- The difference of the two extended-chart representations of `f` is `C^∞` on the product of
the two chart targets. -/
lemma contDiffOn_diff_I {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p q : M) :
    ContDiffOn ℝ ∞ (fun yz : E × E =>
        chartRepI (I := I) f p yz.1 - chartRepI (I := I) f q yz.2)
      {yz | yz.1 ∈ (extChartAt I p).target ∧ yz.2 ∈ (extChartAt I q).target} :=
  ((contDiffOn_chartRepI (I := I) f hf p).comp contDiff_fst.contDiffOn
      (fun _ hyz => hyz.1)).sub
    ((contDiffOn_chartRepI (I := I) f hf q).comp contDiff_snd.contDiffOn
      (fun _ hyz => hyz.2))

/-- The domain of the injectivity-bad parametrisation is open. -/
lemma isOpen_injDomI {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p q : M) :
    IsOpen (injDomI (I := I) f p q) := by
  set T : Set (E × E) :=
    {yz | yz.1 ∈ (extChartAt I p).target ∧ yz.2 ∈ (extChartAt I q).target} with hT
  have hTop : IsOpen T := by
    rw [hT]
    exact ((isOpen_extChartAt_target (I := I) p).preimage continuous_fst).inter
      ((isOpen_extChartAt_target (I := I) q).preimage continuous_snd)
  have hcont : ContinuousOn (fun yz : E × E =>
      (chartRepI (I := I) f p yz.1 - chartRepI (I := I) f q yz.2) (Fin.last k)) T :=
    (by fun_prop : Continuous (fun z : EuclideanSpace ℝ (Fin (k+1)) => z (Fin.last k))
      ).comp_continuousOn (contDiffOn_diff_I (I := I) f hf p q).continuousOn
  have h := hcont.isOpen_inter_preimage hTop (isOpen_compl_singleton (x := (0 : ℝ)))
  have heq : injDomI (I := I) f p q
      = T ∩ (fun yz : E × E =>
          (chartRepI (I := I) f p yz.1 - chartRepI (I := I) f q yz.2) (Fin.last k)) ⁻¹'
          ({0} : Set ℝ)ᶜ := by
    ext yz; simp [injDomI, hT, Set.mem_compl_iff]; tauto
  rw [heq]; exact h

omit [I.Boundaryless] in
/-- The injectivity-bad parametrisation is `C^1` on its domain. -/
lemma contDiffOn_injParamI {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p q : M) :
    ContDiffOn ℝ 1 (injParamI (I := I) f p q) (injDomI (I := I) f p q) := by
  have hdiff : ContDiffOn ℝ ∞ (fun yz : E × E =>
      chartRepI (I := I) f p yz.1 - chartRepI (I := I) f q yz.2)
      (injDomI (I := I) f p q) :=
    (contDiffOn_diff_I (I := I) f hf p q).mono (fun yz hyz => ⟨hyz.1, hyz.2.1⟩)
  have hcomp : ContDiffOn ℝ ∞ (injParamI (I := I) f p q) (injDomI (I := I) f p q) :=
    (contDiffOn_extract_inj k).comp hdiff (fun yz hyz => hyz.2.2)
  exact hcomp.of_le (by simp)

end Helpers

/-- The set of injectivity-bad projection directions of a smooth map from a manifold modelled on
`E` has Hausdorff dimension at most `2 * finrank ℝ E`. -/
theorem dimH_badInjCharts_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p : ℕ → M) :
    dimH (Work.Projection.badInjChartsI (I := I) f p) ≤ (2 * Module.finrank ℝ E : ℕ) := by
  have hsub : badInjChartsI (I := I) f p ⊆
      ⋃ i, ⋃ j, injParamI (I := I) f (p i) (p j) '' injDomI (I := I) f (p i) (p j) :=
    badInjChartsI_subset (I := I) f p
  have hfin : ((Module.finrank ℝ (E × E) : ℕ) : ENNReal)
      = ((2 * Module.finrank ℝ E : ℕ) : ENNReal) := by
    congr 1
    rw [Module.finrank_prod, two_mul]
  calc dimH (badInjChartsI (I := I) f p)
      ≤ dimH (⋃ i, ⋃ j,
          injParamI (I := I) f (p i) (p j) '' injDomI (I := I) f (p i) (p j)) :=
        dimH_mono hsub
    _ = ⨆ i, ⨆ j,
          dimH (injParamI (I := I) f (p i) (p j) '' injDomI (I := I) f (p i) (p j)) := by
        simp only [dimH_iUnion]
    _ ≤ (2 * Module.finrank ℝ E : ℕ) := by
        rw [← hfin]
        refine iSup_le fun i => iSup_le fun j => ?_
        exact dimH_image_le_of_contDiffOn (isOpen_injDomI (I := I) f hf (p i) (p j))
          (contDiffOn_injParamI (I := I) f hf (p i) (p j)) Set.Subset.rfl

end Work.Projection
