import Mathlib
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.T.lc_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound`

The chart Christoffel symbols of the *fixed* initial metric `G 0` of a Ricci flow, read through the
chart at `x₀`, are smooth functions of the chart coordinate, and every iterated Fréchet derivative
of them is bounded on a compact subset of the chart target.

Route.  `cGam g x₀ p l i j` is the `l`-th coordinate of the chart Christoffel symbol `Γ^i_{jl}` of
the Levi-Civita connection `lcOf g`.  The chart Christoffel entries are smooth on the chart source
(`Submission.ChartCurv.contMDiffOn_gammaEntry`, which needs smoothness of `lcOf g`; this is the
`LCSmooth` contract proved in `Submission.Work.Diff.T.lc_smooth`).  Composing with the chart inverse
`(extChartAt I x₀).symm` (smooth on the chart target) gives smoothness on the target, which is open;
smoothness of the `k`-th iterated derivative on an open set
(`ContinuousOn.continuousOn_iteratedFDeriv`) together with compactness of `K` then gives the bound.
-/

set_option linter.style.haveILetI false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The chart Christoffel entries of a smooth metric are smooth on the chart source. -/
theorem cGam_zero_iteratedFDeriv_bound_aux1 (g : SMet I M) (x₀ : M)
    (l i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : M => Work.Diff.GE.cGam g x₀ p l i j) (chartAt H x₀).source := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : ContMDiffCovariantDerivative (lcOf g) ∞ :=
    (Work.Diff.T.lc_smooth (I := I) (M := M) g).1.some
  exact (((Module.finBasis ℝ E).coord l).toContinuousLinearMap).contMDiff.comp_contMDiffOn
    (Submission.ChartCurv.contMDiffOn_gammaEntry (cov := lcOf g) x₀ j i)

/-- The chart Christoffel entries read through the chart at `x₀` are smooth functions of the chart
coordinate, on the chart target. -/
theorem cGam_zero_iteratedFDeriv_bound_aux2 (g : SMet I M) (x₀ : M)
    (l i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : E => Work.Diff.GE.cGam g x₀ (pt (I := I) x₀ y) l i j)
      (extChartAt I x₀).target := by
  have h1 := cGam_zero_iteratedFDeriv_bound_aux1 (I := I) (M := M) g x₀ l i j
  have h2 := contMDiffOn_extChartAt_symm (I := I) (x := x₀) (n := ∞)
  have hmaps : (extChartAt I x₀).target ⊆ (↑(extChartAt I x₀).symm) ⁻¹' (chartAt H x₀).source := by
    intro y hy
    show (extChartAt I x₀).symm y ∈ (chartAt H x₀).source
    simpa only [extChartAt_source] using (extChartAt I x₀).map_target hy
  have h := h1.comp h2 hmaps
  have hfun : ((fun p : M => Work.Diff.GE.cGam g x₀ p l i j) ∘ (↑(extChartAt I x₀).symm))
      = fun y : E => Work.Diff.GE.cGam g x₀ (pt (I := I) x₀ y) l i j := by
    funext y
    simp only [Function.comp_apply, pt]
  rwa [hfun] at h

theorem cGam_zero_iteratedFDeriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K : Set E) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x₀).target) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k
        (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖
        ≤ C := by
  classical
  intro k
  have hb : ∀ p : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
      Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖iteratedFDeriv ℝ k
        (fun y' : E =>
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p.2 p.1.1 p.1.2) y‖
        ≤ C := by
    rintro ⟨⟨i, j⟩, l⟩
    have hcd : ContDiffOn ℝ ∞
        (fun y' : E =>
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') l i j)
        (extChartAt I x₀).target :=
      contMDiffOn_iff_contDiffOn.mp
        (cGam_zero_iteratedFDeriv_bound_aux2 (I := I) (M := M) (G 0) x₀ l i j)
    have hcont : ContinuousOn (iteratedFDeriv ℝ k
        (fun y' : E =>
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') l i j))
        (extChartAt I x₀).target :=
      ContinuousOn.continuousOn_iteratedFDeriv hcd (isOpen_extChartAt_target x₀) (by simp)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKt)
    exact ⟨max C 0, le_max_right _ _,
      fun y hy => le_trans (hC y hy) (le_max_left _ _)⟩
  choose Ci hCi using hb
  refine ⟨∑ p : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
      Fin (Module.finrank ℝ E), Ci p, Finset.sum_nonneg fun p _ => (hCi p).1, ?_⟩
  intro y hy i j l
  exact le_trans ((hCi ((i, j), l)).2 y hy)
    (Finset.single_le_sum (fun p _ => (hCi p).1) (Finset.mem_univ _))

end Work.Diff.EXT
