import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.GraphManifold

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


open scoped Manifold Topology

/-!
# The inclusion of the locally-graph manifold `K` into the ambient space

With the smooth `1`-manifold structure on `↥K` from `GraphManifold.lean`, the inclusion
`Subtype.val : ↥K → ℝⁿ` is a smooth immersion: in the chart at `y` it becomes the graph map
`u ↦ u • eᵢ + η u`, which is smooth with nowhere vanishing derivative (`eᵢ + η'` has `i`-th
coordinate `1`).  Concretely we prove

* `contMDiff_subtype_val_graph` — the inclusion is `C^∞`;
* `mfderiv_subtype_val_injective` — its manifold derivative is injective.
-/

namespace Work.ManifoldParity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold

variable {n : ℕ}

/-- The `i`-th coordinate of the derivative of a function with values in the coordinate
hyperplane `{v | v i = 0}` vanishes. -/
theorem fderiv_coord_eq_zero (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n))
    (hη : ∀ t, η t i = 0) {t : ℝ} (hd : DifferentiableAt ℝ η t) :
    ((fderiv ℝ η t) (1 : ℝ)) i = 0 := by
  have h1 : HasFDerivAt η (fderiv ℝ η t) t := hd.hasFDerivAt
  have h3 : HasFDerivAt (coordProj i ∘ η)
      (((coordProj i).comp (fderiv ℝ η t)) : ℝ →L[ℝ] ℝ) t :=
    HasFDerivAt.comp t (ContinuousLinearMap.hasFDerivAt (coordProj i) (x := η t)) h1
  have h4 : HasFDerivAt (coordProj i ∘ η) (0 : ℝ →L[ℝ] ℝ) t := by
    have hconst : (coordProj i ∘ η) = fun _ : ℝ => (0 : ℝ) :=
      funext fun s => hη s
    rw [hconst]
    exact hasFDerivAt_const (0 : ℝ) t
  have h5 : (coordProj i).comp (fderiv ℝ η t) = 0 := h3.unique h4
  have h6 := congrArg (fun (L : ℝ →L[ℝ] ℝ) => L (1 : ℝ)) h5
  simpa using h6

/-- The derivative of the graph map `chartGraph` applied to `1` never vanishes. -/
theorem chartGraph_fderiv_one_ne_zero (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (y : ↥K) (s : ℝ) :
    (fderiv ℝ (chartGraph K hgra y) s) (1 : ℝ) ≠ 0 := by
  intro h
  set i := (graphChartData K hgra y).idx with hi
  have hηd : DifferentiableAt ℝ (graphChartData K hgra y).eta s :=
    ((graphChartData K hgra y).isChart.2.1.differentiable (by simp)) s
  have hform : (fderiv ℝ (chartGraph K hgra y) s) (1 : ℝ)
      = EuclideanSpace.single (graphChartData K hgra y).idx (1 : ℝ)
        + (fderiv ℝ (graphChartData K hgra y).eta s) (1 : ℝ) := by
    have hlin : HasFDerivAt
        (fun u : ℝ => u • EuclideanSpace.single (graphChartData K hgra y).idx (1 : ℝ))
        (spanSingle (graphChartData K hgra y).idx) s :=
      ContinuousLinearMap.hasFDerivAt (spanSingle (graphChartData K hgra y).idx) (x := s)
    have hsum : HasFDerivAt
        (fun u : ℝ => u • EuclideanSpace.single (graphChartData K hgra y).idx (1 : ℝ)
          + (graphChartData K hgra y).eta u)
        (spanSingle (graphChartData K hgra y).idx + fderiv ℝ (graphChartData K hgra y).eta s) s :=
      hlin.add hηd.hasFDerivAt
    have hsame : chartGraph K hgra y
        = fun u : ℝ => u • EuclideanSpace.single (graphChartData K hgra y).idx (1 : ℝ)
          + (graphChartData K hgra y).eta u := by
      funext u; rw [chartGraph_eq]; rfl
    rw [hsame, hsum.fderiv]
    simp [spanSingle_apply, ContinuousLinearMap.add_apply]
  have hzero : ((fderiv ℝ (graphChartData K hgra y).eta s) (1 : ℝ))
      (graphChartData K hgra y).idx = 0 :=
    fderiv_coord_eq_zero _ _ (graphChartData K hgra y).isChart.2.2.1 hηd
  have hcoord : ((fderiv ℝ (chartGraph K hgra y) s) (1 : ℝ))
      (graphChartData K hgra y).idx = 0 := by
    rw [h]; simp
  rw [hform] at hcoord
  simp only [PiLp.add_apply, PiLp.single_apply, hzero, add_zero] at hcoord
  simpa using hcoord

/-- The derivative of `F u = chartGraph y (e1Proj u)` is injective. -/
theorem fderiv_chartGraph_comp_e1Proj_injective (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (y : ↥K) (u : ME1) :
    Function.Injective (fderiv ℝ (fun u : ME1 => chartGraph K hgra y (e1Proj u)) u) := by
  intro v w hvw
  have hdiff : fderiv ℝ (fun u : ME1 => chartGraph K hgra y (e1Proj u)) u
      = (fderiv ℝ (chartGraph K hgra y) (e1Proj u)).comp e1Proj := by
    have h2 : HasFDerivAt (chartGraph K hgra y)
        (fderiv ℝ (chartGraph K hgra y) (e1Proj u)) (e1Proj u) :=
      (((contDiff_chartGraph K hgra y).differentiable (by simp)) (e1Proj u)).hasFDerivAt
    have h1 : HasFDerivAt (⇑e1Proj : ME1 → ℝ) (e1Proj : ME1 →L[ℝ] ℝ) u :=
      ContinuousLinearMap.hasFDerivAt e1Proj (x := u)
    exact (HasFDerivAt.comp u h2 h1).fderiv
  have h' : fderiv ℝ (chartGraph K hgra y) (e1Proj u) (e1Proj v)
      = fderiv ℝ (chartGraph K hgra y) (e1Proj u) (e1Proj w) := by
    have := hvw
    rw [hdiff] at this
    simpa [ContinuousLinearMap.comp_apply] using this
  have h0 : fderiv ℝ (chartGraph K hgra y) (e1Proj u) (e1Proj (v - w)) = 0 := by
    rw [map_sub e1Proj v w]
    rw [show fderiv ℝ (chartGraph K hgra y) (e1Proj u) (e1Proj v - e1Proj w)
        = fderiv ℝ (chartGraph K hgra y) (e1Proj u) (e1Proj v)
          - fderiv ℝ (chartGraph K hgra y) (e1Proj u) (e1Proj w) from map_sub _ _ _]
    rw [h', sub_self]
  have hlin : fderiv ℝ (chartGraph K hgra y) (e1Proj u) (e1Proj (v - w))
      = (e1Proj (v - w)) • ((fderiv ℝ (chartGraph K hgra y) (e1Proj u)) (1 : ℝ)) := by
    conv_lhs => rw [show e1Proj (v - w) = (e1Proj (v - w)) • (1 : ℝ) from (mul_one _).symm]
    rw [map_smul]
  rw [hlin] at h0
  have hz : e1Proj (v - w) = 0 := by
    rcases smul_eq_zero.mp h0 with h' | h'
    · exact h'
    · exact absurd h' (chartGraph_fderiv_one_ne_zero K hgra y (e1Proj u))
  have hsub : v - w = 0 := by
    have h1 := e1Incl_e1Proj (v - w)
    rw [hz] at h1
    simpa using h1.symm
  exact sub_eq_zero.mp hsub

end

end Work.ManifoldParity

namespace Work.ManifoldParity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set

variable {n : ℕ}

/-- The inclusion `↥K → ℝⁿ` is smooth. -/
theorem contMDiff_subtype_val_graph (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) :
    letI := graphChartedSpace K hgra
    ContMDiff (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) := by
  letI := graphChartedSpace K hgra
  haveI hgr := hasGroupoid_graph K hgra
  haveI hism : IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥K :=
    IsManifold.mk' _ _ _
  intro y
  set F : ME1 → EuclideanSpace ℝ (Fin n) := fun u => chartGraph K hgra y (e1Proj u) with hFdef
  have hFcd : ContMDiff 𝓘(ℝ, ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    rw [contMDiff_iff_contDiff]
    rw [show F = chartGraph K hgra y ∘ e1Proj from rfl]
    exact (contDiff_chartGraph K hgra y).comp e1Proj.contDiff
  have hchart : ContMDiffAt (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (chartAt ME1 y : ↥K → ME1) y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas
      (I := modelWithCornersSelf ℝ ME1) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) y) (mem_chart_source _ _)
  have hcomp : ContMDiffAt (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ (chartAt ME1 y)) y :=
    hFcd.contMDiffAt.comp y hchart
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt ME1 y).open_source.mem_nhds (mem_chart_source _ _)] with y' hy'
  have hyU : y'.1 ∈ (graphChartData K hgra y).U :=
    (mem_chartSource K hgra y).mp (show y' ∈ chartSource K hgra y from hy')
  have hchar := (graphChartData K hgra y).isChart.2.2.2 y'.1 hyU
  show (y' : EuclideanSpace ℝ (Fin n)) = F (chartAt ME1 y y')
  show (y' : EuclideanSpace ℝ (Fin n)) = chartGraph K hgra y (e1Proj (chartAt ME1 y y'))
  rw [show (chartAt ME1 y y') = chartAtK K hgra y y' from rfl, chartAtK_apply, e1Proj_e1Incl]
  rw [chartGraph_eq]
  exact hchar.mp y'.2

/-- The manifold derivative of the inclusion `↥K → ℝⁿ` is injective. -/
theorem mfderiv_subtype_val_injective (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) :
    letI := graphChartedSpace K hgra
    ∀ y : ↥K, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) y) := by
  letI := graphChartedSpace K hgra
  haveI hgr := hasGroupoid_graph K hgra
  haveI hism : IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥K :=
    IsManifold.mk' _ _ _
  intro y
  set c := chartAt ME1 y with hcdef
  set F : ME1 → EuclideanSpace ℝ (Fin n) := fun u => chartGraph K hgra y (e1Proj u) with hFdef
  have hcmd : MDifferentiableAt (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
      (c : ↥K → ME1) y :=
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas
      (I := modelWithCornersSelf ℝ ME1) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) y)
      (mem_chart_source _ _)).mdifferentiableAt (by simp)
  have hc_inj : Function.Injective
      (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1) (c : ↥K → ME1) y) := by
    have hcsmd : MDifferentiableAt (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (c.symm : ME1 → ↥K) (c y) :=
      (contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := modelWithCornersSelf ℝ ME1)
          (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) y)
        (c.map_source (mem_chart_source _ _))).mdifferentiableAt (by simp)
    have hleft : (fun z => c.symm (c z)) =ᶠ[𝓝 y] id :=
      Filter.eventuallyEq_of_mem (c.open_source.mem_nhds (mem_chart_source _ _))
        (fun z hz => c.left_inv hz)
    have hcomp : mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (fun z => c.symm (c z)) y
        = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
            (c.symm : ME1 → ↥K) (c y)) ∘SL
          (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1) (c : ↥K → ME1) y) :=
      mfderiv_comp y hcsmd hcmd
    have hid : mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (fun z => c.symm (c z)) y = ContinuousLinearMap.id ℝ (TangentSpace (modelWithCornersSelf ℝ ME1) y) := by
      rw [Filter.EventuallyEq.mfderiv_eq hleft]
      exact (hasMFDerivAt_id y).mfderiv
    intro a b hab
    calc a = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
            (fun z => c.symm (c z)) y) a := by rw [hid]; rfl
      _ = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
            (c.symm : ME1 → ↥K) (c y))
          ((mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
            (c : ↥K → ME1) y) a) := by rw [hcomp]; rfl
      _ = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
            (c.symm : ME1 → ↥K) (c y))
          ((mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
            (c : ↥K → ME1) y) b) := by rw [hab]
      _ = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
            (fun z => c.symm (c z)) y) b := by rw [hcomp]; rfl
      _ = b := by rw [hid]; rfl
  have hFmd : MDifferentiableAt 𝓘(ℝ, ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F (c y) := by
    have hFcd : ContMDiff 𝓘(ℝ, ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
      rw [contMDiff_iff_contDiff]
      rw [show F = chartGraph K hgra y ∘ e1Proj from rfl]
      exact (contDiff_chartGraph K hgra y).comp e1Proj.contDiff
    exact hFcd.contMDiffAt.mdifferentiableAt (by simp)
  have heq : (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) =ᶠ[𝓝 y] (F ∘ c) := by
    filter_upwards [c.open_source.mem_nhds (mem_chart_source _ _)] with y' hy'
    have hyU : y'.1 ∈ (graphChartData K hgra y).U :=
      (mem_chartSource K hgra y).mp (show y' ∈ chartSource K hgra y from hy')
    have hchar := (graphChartData K hgra y).isChart.2.2.2 y'.1 hyU
    show (y' : EuclideanSpace ℝ (Fin n)) = F (c y')
    show (y' : EuclideanSpace ℝ (Fin n)) = chartGraph K hgra y (e1Proj (c y'))
    rw [show c y' = chartAtK K hgra y y' from rfl, chartAtK_apply, e1Proj_e1Incl]
    rw [chartGraph_eq]
    exact hchar.mp y'.2
  have hmain : mfderiv (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) y
      = (mfderiv 𝓘(ℝ, ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F (c y)) ∘SL
        (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1) (c : ↥K → ME1) y) := by
    rw [Filter.EventuallyEq.mfderiv_eq heq]
    exact mfderiv_comp y hFmd hcmd
  have hkey : ∀ v : TangentSpace (modelWithCornersSelf ℝ ME1) y,
      mfderiv (modelWithCornersSelf ℝ ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) y v
      = mfderiv 𝓘(ℝ, ME1) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F (c y)
        (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (c : ↥K → ME1) y v) := by
    intro v
    rw [hmain]
    rfl
  intro a b hab
  have h1' := hab
  rw [hkey a, hkey b] at h1'
  have h2 : (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (c : ↥K → ME1) y) a
      = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
        (c : ↥K → ME1) y) b := by
    rw [mfderiv_eq_fderiv] at h1'
    rw [show F = (fun u : ME1 => chartGraph K hgra y (e1Proj u)) from rfl] at h1'
    exact fderiv_chartGraph_comp_e1Proj_injective K hgra y (c y) h1'
  exact hc_inj h2

end

end Work.ManifoldParity
