import Mathlib
import Submission.Work.ManifoldParity.Defs

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The smooth `1`-manifold structure of a locally-graph compact set

Let `K ⊆ ℝⁿ` be a set which is *locally the graph of a smooth function over some coordinate axis*
(`Work.ManifoldParity.HasLocalGraphCharts`).  This file endows the subtype `↥K` with the structure
of a smooth `1`-manifold modelled on `EuclideanSpace ℝ (Fin 1)`: the chart at a point is the
restriction of the corresponding coordinate projection, whose inverse is the graph map `gmap`.

The transition functions are the compositions of a graph map with a coordinate projection, hence
smooth; this is `hasGroupoid_graph`.
-/

namespace Work.ManifoldParity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set

variable {n : ℕ}

/-- The model space of a one-dimensional manifold. -/
abbrev ME1 : Type := EuclideanSpace ℝ (Fin 1)

/-- The coordinate functional of `EuclideanSpace ℝ (Fin 1)`. -/
def e1Proj : ME1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0

/-- The `i`-th coordinate projection of `EuclideanSpace ℝ (Fin n)`, as a continuous linear map. -/
def coordProj (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin n => ℝ) i

@[simp]
theorem coordProj_apply (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : coordProj i x = x i := rfl

/-- The map `u ↦ u • eᵢ` of `ℝ` into `EuclideanSpace ℝ (Fin n)`. -/
def spanSingle (i : Fin n) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))

theorem spanSingle_apply (i : Fin n) (u : ℝ) :
    spanSingle i u = u • EuclideanSpace.single i (1 : ℝ) := by
  rw [spanSingle, ContinuousLinearMap.toSpanSingleton_apply]

/-- The inverse of `e1Proj`, as a continuous linear map. -/
def e1Incl : ℝ →L[ℝ] ME1 :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

theorem e1Proj_apply (t : ME1) : e1Proj t = t 0 := rfl

theorem e1Incl_apply (r : ℝ) : e1Incl r = EuclideanSpace.single (0 : Fin 1) r := by
  rw [e1Incl, ContinuousLinearMap.toSpanSingleton_apply]
  ext i
  fin_cases i
  simp

@[simp]
theorem e1Proj_e1Incl (r : ℝ) : e1Proj (e1Incl r) = r := by
  rw [e1Proj_apply, e1Incl_apply]
  simp

theorem e1Incl_e1Proj (t : ME1) : e1Incl (e1Proj t) = t := by
  rw [e1Incl_apply, e1Proj_apply]
  ext i
  fin_cases i
  simp

theorem e1Incl_injective : Function.Injective e1Incl := by
  intro a b h
  simpa using congrArg e1Proj h

/-- The chart data selected at a point of `K` by the local-graph hypothesis. -/
structure GraphChartData (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) where
  /-- The coordinate axis over which `K` is a graph near `x`. -/
  idx : Fin n
  /-- A neighbourhood of `x` on which `K` is the graph. -/
  U : Set (EuclideanSpace ℝ (Fin n))
  /-- The graphing function. -/
  eta : ℝ → EuclideanSpace ℝ (Fin n)
  isChart : IsGraphChart K idx U eta
  mem : x ∈ U

theorem nonempty_graphChartData (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (x : ↥K) : Nonempty (GraphChartData K x.1) := by
  obtain ⟨i, U, η, h⟩ := hgra x.1 x.2
  exact ⟨⟨i, U, η, h.1, h.2⟩⟩

/-- The chart data chosen at a point of `K`. -/
def graphChartData (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) : GraphChartData K x.1 :=
  Classical.choice (nonempty_graphChartData K hgra x)

/-- The graph map of the chosen chart at `x`. -/
def chartGraph (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K) (x : ↥K) :
    ℝ → EuclideanSpace ℝ (Fin n) :=
  gmap (graphChartData K hgra x).idx (graphChartData K hgra x).eta

theorem chartGraph_eq (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) (u : ℝ) :
    chartGraph K hgra x u
      = gmap (graphChartData K hgra x).idx (graphChartData K hgra x).eta u := rfl

theorem chartGraph_coord (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) (u : ℝ) : (chartGraph K hgra x u) (graphChartData K hgra x).idx = u :=
  gmap_coord (graphChartData K hgra x).isChart.2.2.1 u

theorem contDiff_chartGraph (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chartGraph K hgra x) :=
  contDiff_gmap (graphChartData K hgra x).isChart.2.1

/-- The graph point of the chart at `x`, as an element of `K`, when it lies in the chart
neighbourhood. -/
def graphPt (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K) (x : ↥K)
    (u : ℝ) (hu : chartGraph K hgra x u ∈ (graphChartData K hgra x).U) : ↥K :=
  ⟨chartGraph K hgra x u, by
    refine ((graphChartData K hgra x).isChart.2.2.2 _ hu).mpr ?_
    rw [chartGraph_coord]
    rfl⟩

@[simp]
theorem graphPt_val (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) (u : ℝ) (hu : _) : (graphPt K hgra x u hu).1 = chartGraph K hgra x u := rfl

/-- The source of the chart at `x`: the points of `K` lying in the chart neighbourhood. -/
def chartSource (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K) (x : ↥K) :
    Set ↥K :=
  {y | y.1 ∈ (graphChartData K hgra x).U}

/-- The target of the chart at `x`: the parameters whose graph point lies in the chart
neighbourhood. -/
def chartTarget (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K) (x : ↥K) :
    Set ME1 :=
  {t | chartGraph K hgra x (e1Proj t) ∈ (graphChartData K hgra x).U}

theorem mem_chartTarget (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) {t : ME1} :
    t ∈ chartTarget K hgra x ↔ chartGraph K hgra x (e1Proj t) ∈ (graphChartData K hgra x).U :=
  Iff.rfl

theorem mem_chartSource (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) {y : ↥K} :
    y ∈ chartSource K hgra x ↔ y.1 ∈ (graphChartData K hgra x).U :=
  Iff.rfl

/-- The inverse of the chart at `x`, as a total function (with a junk value outside the target). -/
def invFunK (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K) (x : ↥K)
    (t : ME1) : ↥K := by
  classical
  exact if h : chartGraph K hgra x (e1Proj t) ∈ (graphChartData K hgra x).U
    then graphPt K hgra x (e1Proj t) h else ⟨x, x.2⟩

theorem invFunK_eq_of_mem (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) {t : ME1} (ht : t ∈ chartTarget K hgra x) :
    invFunK K hgra x t = graphPt K hgra x (e1Proj t) ht := by
  classical
  rw [invFunK]
  exact dif_pos ht

/-- **The chart at a point of `K`**: the coordinate projection over the axis of the chosen graph
chart, whose inverse is the graph map. -/
def chartAtK (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K) (x : ↥K) :
    OpenPartialHomeomorph ↥K ME1 where
  toFun := fun y => e1Incl (y.1 (graphChartData K hgra x).idx)
  invFun := invFunK K hgra x
  source := chartSource K hgra x
  target := chartTarget K hgra x
  map_source' := by
    intro y hy
    rw [mem_chartTarget]
    show chartGraph K hgra x (e1Proj (e1Incl (y.1 (graphChartData K hgra x).idx)))
      ∈ (graphChartData K hgra x).U
    rw [e1Proj_e1Incl, chartGraph_eq]
    have h := (graphChartData K hgra x).isChart.2.2.2 y.1 ((mem_chartSource K hgra x).mp hy)
    rw [← h.mp y.2]
    exact (mem_chartSource K hgra x).mp hy
  map_target' := by
    intro t ht
    rw [mem_chartSource]
    rw [invFunK_eq_of_mem K hgra x ht]
    exact (mem_chartTarget K hgra x).mp ht
  left_inv' := by
    intro y hy
    have hyU : y.1 ∈ (graphChartData K hgra x).U := (mem_chartSource K hgra x).mp hy
    have hchar := (graphChartData K hgra x).isChart.2.2.2 y.1 hyU
    have hyK : y.1 = chartGraph K hgra x (y.1 (graphChartData K hgra x).idx) := by
      rw [chartGraph_eq]; exact hchar.mp y.2
    have hmem : (e1Incl (y.1 (graphChartData K hgra x).idx)) ∈ chartTarget K hgra x := by
      rw [mem_chartTarget, e1Proj_e1Incl, ← hyK]
      exact hyU
    show invFunK K hgra x (e1Incl (y.1 (graphChartData K hgra x).idx)) = y
    rw [invFunK_eq_of_mem K hgra x hmem]
    apply Subtype.ext
    rw [graphPt_val, e1Proj_e1Incl]
    exact hyK.symm
  right_inv' := by
    intro t ht
    show e1Incl ((invFunK K hgra x t).1 (graphChartData K hgra x).idx) = t
    rw [invFunK_eq_of_mem K hgra x ht]
    simp only [graphPt_val]
    rw [chartGraph_coord, e1Incl_e1Proj]
  open_source := (graphChartData K hgra x).isChart.1.preimage continuous_subtype_val
  open_target := (graphChartData K hgra x).isChart.1.preimage
    ((contDiff_chartGraph K hgra x).continuous.comp e1Proj.continuous)
  continuousOn_toFun := by
    refine Continuous.continuousOn ?_
    fun_prop
  continuousOn_invFun := by
    classical
    rw [continuousOn_iff_continuous_restrict]
    have hcont1 : Continuous (fun t : ↥(chartTarget K hgra x) =>
        chartGraph K hgra x (e1Proj (t : ME1))) :=
      ((contDiff_chartGraph K hgra x).continuous.comp e1Proj.continuous).comp
        continuous_subtype_val
    have hcont2 : Continuous (fun t : ↥(chartTarget K hgra x) =>
        (⟨chartGraph K hgra x (e1Proj (t : ME1)), by
          have ht : chartGraph K hgra x (e1Proj (t : ME1)) ∈ (graphChartData K hgra x).U :=
            (mem_chartTarget K hgra x).mp t.2
          exact ((graphChartData K hgra x).isChart.2.2.2 _ ht).mpr
            (by rw [chartGraph_coord, chartGraph_eq])⟩ : ↥K)) :=
      hcont1.subtype_mk (fun t => by
        have ht : chartGraph K hgra x (e1Proj (t : ME1)) ∈ (graphChartData K hgra x).U :=
          (mem_chartTarget K hgra x).mp t.2
        exact ((graphChartData K hgra x).isChart.2.2.2 _ ht).mpr
          (by rw [chartGraph_coord, chartGraph_eq]))
    refine Continuous.congr hcont2 ?_
    intro t
    have ht : (t : ME1) ∈ chartTarget K hgra x := t.2
    show (⟨chartGraph K hgra x (e1Proj (t : ME1)), _⟩ : ↥K) = invFunK K hgra x (t : ME1)
    rw [invFunK_eq_of_mem K hgra x ht]
    exact Subtype.ext rfl

theorem chartAtK_source (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) : (chartAtK K hgra x).source = chartSource K hgra x := rfl

theorem chartAtK_target (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) : (chartAtK K hgra x).target = chartTarget K hgra x := rfl

/-- The charted space structure on `↥K` given by the graph charts. -/
@[instance_reducible]
def graphChartedSpace (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K) :
    ChartedSpace ME1 ↥K where
  atlas := Set.range (chartAtK K hgra)
  chartAt := chartAtK K hgra
  mem_chart_source := fun x => (graphChartData K hgra x).mem
  chart_mem_atlas := fun x => ⟨x, rfl⟩

theorem graphChartedSpace_chartAt (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (x : ↥K) :
    @ChartedSpace.chartAt ME1 _ ↥K _ (graphChartedSpace K hgra) x = chartAtK K hgra x := rfl

end

end Work.ManifoldParity

namespace Work.ManifoldParity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set

variable {n : ℕ}

theorem chartAtK_apply (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) (y : ↥K) :
    chartAtK K hgra x y = e1Incl (y.1 (graphChartData K hgra x).idx) := rfl

theorem chartAtK_symm_apply (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K)
    (x : ↥K) {t : ME1} (ht : t ∈ (chartAtK K hgra x).target) :
    (chartAtK K hgra x).symm t
      = graphPt K hgra x (e1Proj t) ((mem_chartTarget K hgra x).mp ht) := by
  show invFunK K hgra x t = graphPt K hgra x (e1Proj t) _
  exact invFunK_eq_of_mem K hgra x ((mem_chartTarget K hgra x).mp ht)

theorem contDiff_transitionFun (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (x x' : ↥K) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ME1 => e1Incl ((chartGraph K hgra x (e1Proj t))
        (graphChartData K hgra x').idx)) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ME1 => chartGraph K hgra x (e1Proj t)) :=
    (contDiff_chartGraph K hgra x).comp e1Proj.contDiff
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : EuclideanSpace ℝ (Fin n) => v (graphChartData K hgra x').idx) := by
    fun_prop
  exact e1Incl.contDiff.comp (h2.comp h1)

theorem contDiffOn_transition (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (x x' : ↥K) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑(OpenPartialHomeomorph.trans (chartAtK K hgra x).symm (chartAtK K hgra x')))
      ((OpenPartialHomeomorph.trans (chartAtK K hgra x).symm (chartAtK K hgra x')).source) := by
  refine (contDiff_transitionFun K hgra x x').contDiffOn.congr ?_
  intro t ht
  rw [OpenPartialHomeomorph.coe_trans]
  have htmem := ht
  rw [OpenPartialHomeomorph.trans_source] at htmem
  have ht' : t ∈ (chartAtK K hgra x).target := htmem.1
  have hs' : (chartAtK K hgra x).symm t ∈ (chartAtK K hgra x').source := htmem.2
  show (chartAtK K hgra x') ((chartAtK K hgra x).symm t) = _
  rw [chartAtK_apply, chartAtK_symm_apply K hgra x ht', graphPt_val]

theorem hasGroupoid_graph (K : Set (EuclideanSpace ℝ (Fin n))) (hgra : HasLocalGraphCharts K) :
    @HasGroupoid ME1 _ ↥K _ (graphChartedSpace K hgra)
      (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) (modelWithCornersSelf ℝ ME1)) := by
  letI := graphChartedSpace K hgra
  refine hasGroupoid_of_pregroupoid _ (fun {e e'} he he' => ?_)
  obtain ⟨x, rfl⟩ := he
  obtain ⟨x', rfl⟩ := he'
  simp only [contDiffPregroupoid]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.preimage_id, Set.univ_inter, Set.inter_univ, Set.range_id]
  exact contDiffOn_transition K hgra x x'

end

end Work.ManifoldParity
