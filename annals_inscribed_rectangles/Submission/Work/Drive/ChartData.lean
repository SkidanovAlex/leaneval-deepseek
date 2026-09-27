import Mathlib
import Submission.Work.Drive.BoxParityDefs

/-!
# Charts for the zero set of `F`

A `ChartData F p` is the data of a *local chart* for the zero set of `F : ℝ^{m+1} → ℝ^m` near a
point `p`, together with a lower bound for the `i`-th component of the flow field on the chart:

* `i` is the index of the "tangential" coordinate;
* `η : ℝ → ℝ^{m+1}` parametrises the zero set as the graph of `u ↦ u • eᵢ + η u`, which lies in
  the coordinate hyperplane `(·) i = 0` transversally, i.e. `η u i = 0` for all `u`;
* `δ, ρ > 0` are the radii of the chart region `region = {x | |x i - p i| < δ}` intersected with
  `{x | ‖x - (x i) • eᵢ - η (x i)‖ < ρ}` (a tubular neighbourhood of the graph);
* `hgraph` says that inside the region the zero set of `F` is *exactly* the graph;
* `c > 0` is a lower bound for `|flowField F x i|` on the region.

The main consumer is `Work.Drive.chart_visit_bddAbove`: a flow line of `flowField F` cannot stay in
the region of a chart for unbounded time (because its `i`-th coordinate moves at speed at least
`c` and is trapped in the interval `(p i - δ, p i + δ)`).
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

noncomputable section

/-- Local chart data for the zero set of `F` near `p`. -/
structure ChartData {m : ℕ} (F : Amb m → Tgt m) (p : Amb m) where
  /-- The index of the tangential coordinate. -/
  i : Fin (m + 1)
  /-- Radius of the chart in the `i`-th coordinate. -/
  δ : ℝ
  /-- Radius of the chart in the normal direction to the graph. -/
  ρ : ℝ
  /-- Lower bound for the `i`-th component of the flow field on the chart region. -/
  c : ℝ
  /-- The parametrisation of the zero set: the graph of `u ↦ u • eᵢ + η u`. -/
  η : ℝ → Amb m
  hδ : 0 < δ
  hρ : 0 < ρ
  hc : 0 < c
  hηc : Continuous η
  hηi : ∀ u, η u i = 0
  hgraph : ∀ x, |x i - p i| < δ →
    ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ → F x = 0 →
    x = (x i) • EuclideanSpace.single i 1 + η (x i)
  hvel : ∀ x, |x i - p i| < δ →
    ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ → c ≤ |flowField F x i|

/-- The graph map `u ↦ u • eᵢ + η u` of a chart. -/
def ChartData.graph {m : ℕ} {F : Amb m → Tgt m} {p : Amb m} (C : ChartData F p) : ℝ → Amb m :=
  fun u => u • EuclideanSpace.single C.i (1 : ℝ) + C.η u

/-- The region of a chart: the tubular neighbourhood of the graph on which the chart is valid. -/
def ChartData.region {m : ℕ} {F : Amb m → Tgt m} {p : Amb m} (C : ChartData F p) :
    Set (Amb m) :=
  {x | |x C.i - p C.i| < C.δ ∧
    ‖x - (x C.i) • EuclideanSpace.single C.i (1 : ℝ) - C.η (x C.i)‖ < C.ρ}

@[simp] theorem ChartData.mem_region {m : ℕ} {F : Amb m → Tgt m} {p : Amb m}
    (C : ChartData F p) (x : Amb m) :
    x ∈ C.region ↔ |x C.i - p C.i| < C.δ ∧
      ‖x - (x C.i) • EuclideanSpace.single C.i (1 : ℝ) - C.η (x C.i)‖ < C.ρ := Iff.rfl

/-- The coordinate of the graph point at parameter `u` is `u`. -/
theorem ChartData.graph_apply_i {m : ℕ} {F : Amb m → Tgt m} {p : Amb m} (C : ChartData F p)
    (u : ℝ) : C.graph u C.i = u := by
  simp [ChartData.graph, PiLp.add_apply, PiLp.smul_apply, C.hηi u]

/-- A point of the graph over the slab `|u - p i| < δ` lies in the region of the chart. -/
theorem ChartData.graph_mem_region {m : ℕ} {F : Amb m → Tgt m} {p : Amb m} (C : ChartData F p)
    {u : ℝ} (hu : |u - p C.i| < C.δ) : C.graph u ∈ C.region := by
  have hci : (u • EuclideanSpace.single C.i (1 : ℝ) + C.η u).ofLp C.i = u := by
    simp [PiLp.add_apply, PiLp.smul_apply, C.hηi u]
  rw [ChartData.mem_region]
  refine ⟨?_, ?_⟩
  · show |(u • EuclideanSpace.single C.i (1 : ℝ) + C.η u).ofLp C.i - p.ofLp C.i| < C.δ
    rw [hci]
    exact hu
  · show ‖u • EuclideanSpace.single C.i (1 : ℝ) + C.η u -
      (u • EuclideanSpace.single C.i (1 : ℝ) + C.η u).ofLp C.i •
        EuclideanSpace.single C.i (1 : ℝ) - C.η ((u • EuclideanSpace.single C.i (1 : ℝ) +
          C.η u).ofLp C.i)‖ < C.ρ
    rw [hci]
    have h0 : u • EuclideanSpace.single C.i (1 : ℝ) + C.η u -
        u • EuclideanSpace.single C.i (1 : ℝ) - C.η u = 0 := by abel
    rw [h0, norm_zero]
    exact C.hρ

/-- The region of a chart is open. -/
theorem ChartData.isOpen_region {m : ℕ} {F : Amb m → Tgt m} {p : Amb m} (C : ChartData F p) :
    IsOpen C.region := by
  have h1 : Continuous fun x : Amb m => |x C.i - p C.i| := by fun_prop
  have h2 : Continuous fun x : Amb m => ‖x - (x C.i) • EuclideanSpace.single C.i (1 : ℝ) -
      C.η (x C.i)‖ := by
    have : Continuous fun x : Amb m => C.η (x C.i) := C.hηc.comp (by fun_prop)
    fun_prop
  rw [ChartData.region]
  exact isOpen_lt h1 continuous_const |>.inter (isOpen_lt h2 continuous_const)

/-- A zero of `F` in the region of a chart lies on the graph. -/
theorem ChartData.eq_graph_of_mem_region {m : ℕ} {F : Amb m → Tgt m} {p : Amb m}
    (C : ChartData F p) {x : Amb m} (hx : x ∈ C.region) (hF : F x = 0) :
    x = C.graph (x C.i) := by
  rw [ChartData.mem_region] at hx
  exact C.hgraph x hx.1 hx.2 hF

/-- Continuity of the graph map of a chart. -/
theorem ChartData.continuous_graph {m : ℕ} {F : Amb m → Tgt m} {p : Amb m}
    (C : ChartData F p) : Continuous C.graph := by
  have : C.graph = fun u => u • EuclideanSpace.single C.i (1 : ℝ) + C.η u := rfl
  rw [this]
  exact ((continuous_id.smul continuous_const).add C.hηc)

end

end Work.Drive
