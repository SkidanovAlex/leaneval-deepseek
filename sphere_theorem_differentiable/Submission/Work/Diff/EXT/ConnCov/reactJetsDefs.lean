import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the jet bounds of the reaction array `∂_t aComp`

This module (definitions only) fixes the chart-level objects appearing in the statement
`Work.Diff.EXT.ConnCov.reactArr_jets`, so that the pieces of its proof can be stated compactly.

With `n = Module.finrank ℝ E`, `σ_a = cFrame x₀ a` the coordinate frame of the chart at `x₀`, and
`y : E` a chart coordinate (`pt x₀ y = (extChartAt I x₀).symm y`):

* `ricFun G x₀ t y a b = Ric_{ab}(G t)(y) = ricAt (lcOf (G t)) (pt y) (σ_a) (σ_b)` is the
  `(a,b)` entry of `Work.Diff.EXT.chartRicMat (G t) x₀ y`;
* `ricArr G x₀ t y a b = ∑_{k,l} γ^{kl}(t,y) R_{kalb}(t,y)` is the *same* quantity written as the
  inverse-Gram contraction of the chart curvature array `Work.Diff.GE.rmChartExpr`
  (the bridge `ricFun = ricArr` is the standard trace identity in the coordinate frame, proved from
  `Work.Diff.EXT.ricAt_invGram_chart` and `Work.Diff.EXT.pcj_rmC4_rmChartExpr`);
* `reactExpr G x₀ i j l t y` is the explicit chart expression of the reaction array
  `Work.Diff.EXT.ConnCov.reactArr = ∂_t aComp`:
  `∂_t aComp_{ijl} = -(∂_i Ric_{jl} + ∂_j Ric_{il} - ∂_l Ric_{ij}) + 2 ∑_p Ric_{lp} Γ^p_{ij}(G 0)`.

The point of these definitions is that `reactExpr` is an *algebraic* expression in the chart jets of
`chartMat` (through `GramInv` and `rmChartExpr`, i.e. through the inverse chart matrix and the chart
curvature) and in the *fixed* Christoffel symbols `cGam (G 0)`; hence its iterated Fréchet
derivatives at the points of a compact `K'` are bounded by the chart jets of `chartMat` (order
`K + 1`), of `rmChartExpr` (order `K + 1`) and the determinant lower bound for `GramM`.

## WARNING: the statement `Work.Diff.EXT.ConnCov.reactArr_jets` is mis-stated (binder shadowing)

Its conclusion is written

`∃ Cd, 0 ≤ Cd ∧ ∀ t ∈ Ico (T/2) T, ∀ j : ℕ, j ≤ K → ∀ (i j l : Fin n), ∀ y ∈ K',
   ‖iteratedFDeriv ℝ j (...) y‖ ≤ Cd`

so the derivative order in the *body* is the **`Fin` index `j`** (which shadows the `ℕ` binder
`j`), i.e. the conclusion demands bounds for the derivative orders `0, …, n - 1` — *independently of
`K`* — while the hypothesis `j ≤ K` is vacuous.  (Verified by elaborating
`example : (∀ j : ℕ, j ≤ 0 → ∀ (i j l : Fin 3), (j : ℕ) ≤ 2) := fun j _ i j l => j.isLt`.)

The *intended* statement (and the one needed by `dAOfTower_chart_bound`/`tower3Arr_jets`) is the
same with a *fresh* name for the order,

`∃ Cd, 0 ≤ Cd ∧ ∀ t ∈ Ico (T/2) T, ∀ (m : ℕ), m ≤ K → ∀ (i j l : Fin n), ∀ y ∈ K',
   ‖iteratedFDeriv ℝ m (...) y‖ ≤ Cd`

and it is the one proved (for `reactExpr`) in `Work.Diff.EXT.ConnCov.reactJetsKit`.  This is *not*
an entirely cosmetic difference: for `K + 2 < n` the mis-stated version asks for bounds on
derivatives of order up to `n - 1`, whereas the hypotheses (`hrm`, `hmat`) only control the chart
jets of order `≤ K + 1`; obtaining the higher orders would require a completely different (and much
larger) argument from `hShi`/`hbound`/`hmet` (all-order chart bounds at *arbitrary* points, not just
near the chart centre as in `Work.Diff.EXT.chartBounds_of_shibounds`).
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The Ricci tensor of `G t`, read in the coordinate frame of the chart at `x₀`, as a function of
the chart coordinate `y`: the `(a,b)` entry of `Work.Diff.EXT.chartRicMat (G t) x₀ y`. -/
noncomputable def ricFun (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (y : E)
    (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) (Work.Diff.EXT.pt (I := I) x₀ y)
    (Work.Diff.GE.cFrame (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y))
    (Work.Diff.GE.cFrame (I := I) x₀ b (Work.Diff.EXT.pt (I := I) x₀ y))

/-- The chart Ricci components written as the inverse-Gram contraction of the chart curvature
array: `Ric_{ab}(t,y) = ∑_{k,l} γ^{kl}(t,y) · R_{kalb}(t,y)`.  Pointwise equal to `ricFun`
(the trace identity in the coordinate frame). -/
noncomputable def ricArr (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (y : E)
    (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ k, ∑ l, Work.Diff.GE.GramInv (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) k l
    * Work.Diff.GE.rmChartExpr (I := I) G x₀ k a l b t (Work.Diff.EXT.pt (I := I) x₀ y)

/-- **The explicit chart expression of the reaction array** `∂_t aComp`:
`∂_t aComp_{ijl} = -(∂_i Ric_{jl} + ∂_j Ric_{il} - ∂_l Ric_{ij}) + 2 ∑_p Ric_{lp} Γ^p_{ij}(G 0)`,
where the partial derivatives are those of the chart function `y ↦ Ric_{ab}(t,y)` in the
directions of the basis of the model space, and `Γ^p_{ij}(G 0)` are the Christoffel symbols of the
*fixed* initial metric in the coordinate frame. -/
noncomputable def reactExpr (G : ℝ → Submission.Diff.SMet I M) (x₀ : M)
    (i j l : Fin (Module.finrank ℝ E)) (t : ℝ) (y : E) : ℝ :=
  - (fderiv ℝ (fun y' : E => ricArr G x₀ t y' j l) y (Work.Diff.EXT.bB (E := E) i)
     + fderiv ℝ (fun y' : E => ricArr G x₀ t y' i l) y (Work.Diff.EXT.bB (E := E) j)
     - fderiv ℝ (fun y' : E => ricArr G x₀ t y' i j) y (Work.Diff.EXT.bB (E := E) l))
  + 2 * ∑ p : Fin (Module.finrank ℝ E),
      ricArr G x₀ t y l p * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j

end Work.Diff.EXT.ConnCov
