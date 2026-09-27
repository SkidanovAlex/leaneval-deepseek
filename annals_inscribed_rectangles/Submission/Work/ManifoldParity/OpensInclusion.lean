import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.GraphManifold
import Submission.Work.ManifoldParity.GraphInclusion

/-!
# Smooth immersions from open subsets of the locally-graph manifold

For an open subset `s` of `↥K` (endowed with the restricted charted space structure of
`TopologicalSpace.Opens.instChartedSpace`), the map `z ↦ ((z : ↥K) : ℝⁿ)` is a smooth immersion
whose manifold derivative is injective.  This is what allows a parametrisation of a *component* of
`K` to be read in the ambient space.
-/

open scoped Manifold Topology

namespace Work.ManifoldParity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set

variable {n : ℕ}

/-- The manifold derivative of a chart is injective. -/
theorem mfderiv_chartAt_injective {M : Type*} [TopologicalSpace M] [ChartedSpace ME1 M]
    [IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) M] (x : M) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (chartAt ME1 x : M → ME1) x) := by
  set c := chartAt ME1 x with hc
  have hcmd : MDifferentiableAt (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (c : M → ME1) x :=
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas
      (I := modelWithCornersSelf ℝ ME1) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) x)
      (mem_chart_source _ _)).mdifferentiableAt (by simp)
  have hcsmd : MDifferentiableAt (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (c.symm : ME1 → M) (c x) :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := modelWithCornersSelf ℝ ME1)
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) x)
      (c.map_source (mem_chart_source _ _))).mdifferentiableAt (by simp)
  have hleft : (fun z => c.symm (c z)) =ᶠ[𝓝 x] id :=
    Filter.eventuallyEq_of_mem (c.open_source.mem_nhds (mem_chart_source _ _))
      (fun z hz => c.left_inv hz)
  have hcomp : mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (fun z => c.symm (c z)) x
      = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (c.symm : ME1 → M) (c x)) ∘SL
        (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1) (c : M → ME1) x) :=
    mfderiv_comp x hcsmd hcmd
  have hid : mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (fun z => c.symm (c z)) x
      = ContinuousLinearMap.id ℝ (TangentSpace (modelWithCornersSelf ℝ ME1) x) := by
    rw [Filter.EventuallyEq.mfderiv_eq hleft]
    exact (hasMFDerivAt_id x).mfderiv
  intro a b hab
  calc a = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (fun z => c.symm (c z)) x) a := by rw [hid]; rfl
    _ = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (c.symm : ME1 → M) (c x))
        ((mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (c : M → ME1) x) a) := by rw [hcomp]; rfl
    _ = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (c.symm : ME1 → M) (c x))
        ((mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (c : M → ME1) x) b) := by rw [hab]
    _ = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (fun z => c.symm (c z)) x) b := by rw [hcomp]; rfl
    _ = b := by rw [hid]; rfl

/-- The manifold derivative of the inclusion of an open subset is injective. -/
theorem mfderiv_subtypeVal_opens_injective {M : Type*} [TopologicalSpace M] [ChartedSpace ME1 M]
    [IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (s : TopologicalSpace.Opens M) (x : s) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (Subtype.val : s → M) x) := by
  have heq : (fun z : s => chartAt ME1 (x : M) (z : M))
      =ᶠ[𝓝 x] (chartAt ME1 x : s → ME1) := by
    refine Filter.eventuallyEq_of_mem
      ((chartAt ME1 x).open_source.mem_nhds (mem_chart_source _ _)) ?_
    intro z hz
    rw [TopologicalSpace.Opens.chartAt_eq]
    rfl
  have hmd2 : MDifferentiableAt (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (chartAt ME1 (x : M) : M → ME1) (x : M) :=
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas
      (I := modelWithCornersSelf ℝ ME1) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x : M))
      (mem_chart_source _ _)).mdifferentiableAt (by simp)
  have hmd1 : MDifferentiableAt (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (Subtype.val : s → M) x :=
    ((Manifold.IsSmoothEmbedding.of_opens (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) s).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hchain : mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (chartAt ME1 x : s → ME1) x
      = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (chartAt ME1 (x : M) : M → ME1) (x : M)) ∘SL
        (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (Subtype.val : s → M) x) := by
    rw [Filter.EventuallyEq.mfderiv_eq heq.symm]
    ext v
    exact congrArg (fun L => L v) (mfderiv_comp x hmd2 hmd1)
  intro a b hab
  have hfab : (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (chartAt ME1 (x : M) : M → ME1) (x : M))
      ((mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (Subtype.val : s → M) x) a)
      = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (chartAt ME1 (x : M) : M → ME1) (x : M))
      ((mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (Subtype.val : s → M) x) b) := by
    rw [hab]
  refine mfderiv_chartAt_injective (M := s) x ?_
  rw [hchain]
  exact hfab

/-- The map `z ↦ ((z : ↥K) : ℝⁿ)` from an open subset of `↥K` to the ambient space is a smooth
immersion. -/
theorem contMDiff_subtype_val_opens_graph (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (s : TopologicalSpace.Opens ↥K) :
    letI := graphChartedSpace K hgra
    ContMDiff (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : s => ((z : ↥K) : EuclideanSpace ℝ (Fin n))) := by
  letI := graphChartedSpace K hgra
  haveI hgr := hasGroupoid_graph K hgra
  haveI hism : IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥K :=
    IsManifold.mk' _ _ _
  have hι : ContMDiff (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) :=
    contMDiff_subtype_val_graph K hgra
  exact hι.comp (Manifold.IsSmoothEmbedding.of_opens (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) s).contMDiff

/-- The manifold derivative of the map `z ↦ ((z : ↥K) : ℝⁿ)` from an open subset of `↥K` to the
ambient space is injective. -/
theorem mfderiv_subtype_val_opens_graph_injective (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) :
    letI := graphChartedSpace K hgra
    ∀ (s : TopologicalSpace.Opens ↥K) (z : s),
      Function.Injective (mfderiv (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun z : s => ((z : ↥K) : EuclideanSpace ℝ (Fin n))) z) := by
  letI := graphChartedSpace K hgra
  haveI hgr := hasGroupoid_graph K hgra
  haveI hism : IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥K :=
    IsManifold.mk' _ _ _
  intro s z a b hab
  have hι : ContMDiff (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) :=
    contMDiff_subtype_val_graph K hgra
  have hchain : mfderiv (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun z : s => ((z : ↥K) : EuclideanSpace ℝ (Fin n))) z
      = (mfderiv (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) (z : ↥K)) ∘SL
        (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (Subtype.val : s → ↥K) z) :=
    mfderiv_comp z (hι.contMDiffAt.mdifferentiableAt (by simp))
      ((Manifold.IsSmoothEmbedding.of_opens (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) s).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have h1 : mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (Subtype.val : s → ↥K) z a
      = mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (Subtype.val : s → ↥K) z b := by
    apply mfderiv_subtype_val_injective K hgra (z : ↥K)
    have h := hab
    rw [hchain] at h
    simpa only [ContinuousLinearMap.comp_apply] using h
  exact mfderiv_subtypeVal_opens_injective s z h1

end

end Work.ManifoldParity
