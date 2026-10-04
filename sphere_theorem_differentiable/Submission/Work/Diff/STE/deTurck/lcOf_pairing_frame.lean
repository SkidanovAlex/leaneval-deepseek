import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.GE.covRmChartExpr_eq
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.T.lc_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pairing of `∇_{σ_i} W` with the coordinate frame

For a smooth metric `g`, the Levi-Civita connection `∇ = lcOf g` and the coordinate frame
`σ_i = cFrame x₀ i` of the chart at `x₀` one has, at every point `y` of the chart,

`⟨∇_{σ_i} W, σ_j⟩ = σ_i⟨W, σ_j⟩ - ∑_c Γ^c_{ij} ⟨W, σ_c⟩`

(`Γ^c_{ij} = chrCoord g x₀ c i j` are the Christoffel symbols of the frame), for every smooth
vector field `W`.  This is metric compatibility `σ_i⟨W,σ_j⟩ = ⟨∇_{σ_i}W,σ_j⟩ + ⟨W,∇_{σ_i}σ_j⟩`
combined with the chart formula `∇_{σ_i}σ_j = ∑_c Γ^c_{ij} σ_c` of the coordinate frame.

The chart formula for the connection on the frame is
`Work.Diff.GE.CovRmChartAux.lcOf_field_eq_sum_chrCoord`; metric compatibility of `lcOf g` is
`hLC g` (contract T1); the frame vector `σ_j` is globalised to a smooth section with
`Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection` so that the
challenge's `IsMetricCompatible` — which quantifies over *globally* smooth sections — applies.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.deTurck

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

noncomputable section

/-- **Metric compatibility in the coordinate frame.**  For a smooth metric `g`, a smooth vector
field `W` and a point `y` of the chart at `x₀`, the pairing of `∇_{σ_i} W` with the `j`-th
coordinate frame vector is the derivative of `⟨W, σ_j⟩` in the direction `σ_i`, corrected by the
Christoffel symbols `Γ^c_{ij}` of the frame. -/
theorem lcOf_pairing_frame_chart
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    {W : Π q : M, TangentSpace I q} (hW : Work.Diff.EXT.SmoothTField (I := I) (M := M) W)
    (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    (G t).inner y ((Submission.Diff.lcOf (G t)) W y (Work.Diff.GE.cFrame (I := I) x₀ i y))
        (Work.Diff.GE.cFrame (I := I) x₀ j y)
      = mvfderiv I (fun q : M => (G t).inner q (W q) (Work.Diff.GE.cFrame (I := I) x₀ j q))
          y (Work.Diff.GE.cFrame (I := I) x₀ i y)
        - ∑ c : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ c i j t y
              * (G t).inner y (W y) (Work.Diff.GE.cFrame (I := I) x₀ c y) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨-, -, hmet⟩ := hLC (G t)
  -- a globally smooth section agreeing with the frame vector `σ_j` near `y`
  obtain ⟨Z, hZsm, hZeq⟩ :=
    Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀
      (Work.Diff.GE.cBasis (E := E) j) hy
  have hZy : Z y = Work.Diff.GE.cFrame (I := I) x₀ j y := by
    rw [hZeq.self_of_nhds]; rfl
  -- metric compatibility for `(W, Z)` in the direction `σ_i`
  have hmetYZ := hmet W Z hW hZsm y (Work.Diff.GE.cFrame (I := I) x₀ i y)
  -- the chart formula `∇_{σ_i} σ_j = ∑_c Γ^c_{ij} σ_c`
  have hconn :=
    Work.Diff.GE.CovRmChartAux.lcOf_field_eq_sum_chrCoord (I := I) hLC G x₀ hy t i j hZsm hZeq
  -- replace `Z` by the frame vector in the `mvfderiv` of the pairing
  have hgerm : (fun q : M => inner ℝ (W q) (Z q))
      =ᶠ[𝓝 y] (fun q : M => (G t).inner q (W q) (Work.Diff.GE.cFrame (I := I) x₀ j q)) := by
    filter_upwards [hZeq] with q hq
    rw [hq]
    rfl
  rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hgerm] at hmetYZ
  rw [hZy] at hmetYZ
  -- the pairing with `∇_{σ_i}σ_j = ∑_c Γ^c_{ij} σ_c`
  have hsum : inner ℝ (W y)
        (Submission.Diff.lcOf (G t) Z y (Work.Diff.GE.cFrame (I := I) x₀ i y))
      = ∑ c : Fin (Module.finrank ℝ E), Work.Diff.GE.chrCoord (I := I) G x₀ c i j t y
          * (G t).inner y (W y) (Work.Diff.GE.cFrame (I := I) x₀ c y) := by
    rw [hconn]
    simp only [inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl (fun c _ => rfl)
  have hinner : ∀ (u v : TangentSpace I y), inner ℝ u v = (G t).inner y u v :=
    fun _ _ => rfl
  have hkey : (G t).inner y (Submission.Diff.lcOf (G t) W y (Work.Diff.GE.cFrame (I := I) x₀ i y))
        (Work.Diff.GE.cFrame (I := I) x₀ j y)
      = mvfderiv I (fun q : M => (G t).inner q (W q) (Work.Diff.GE.cFrame (I := I) x₀ j q))
          y (Work.Diff.GE.cFrame (I := I) x₀ i y)
        - inner ℝ (W y)
            (Submission.Diff.lcOf (G t) Z y (Work.Diff.GE.cFrame (I := I) x₀ i y)) := by
    rw [hmetYZ]; simp only [hinner]; ring
  rw [hkey, hsum]

end

theorem lcOf_pairing_frame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {W : Π q : M, TangentSpace I q} (hW : Work.Diff.EXT.SmoothTField (I := I) (M := M) W)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) (i j : Fin (Module.finrank ℝ E)) :
    g.inner ((extChartAt I x₀).symm y)
        (Submission.Diff.lcOf g W ((extChartAt I x₀).symm y)
          (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y)))
        (Work.Diff.GE.cFrame (I := I) x₀ j ((extChartAt I x₀).symm y))
      = mvfderiv I (fun q : M => g.inner q (W q) (Work.Diff.GE.cFrame (I := I) x₀ j q))
          ((extChartAt I x₀).symm y)
          (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
        - ∑ c : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (fun _ : ℝ => g) (I := I) x₀ c i j 0
              ((extChartAt I x₀).symm y)
              * g.inner ((extChartAt I x₀).symm y) (W ((extChartAt I x₀).symm y))
                  (Work.Diff.GE.cFrame (I := I) x₀ c ((extChartAt I x₀).symm y)) := by
  have hsrc : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact (extChartAt I x₀).map_target hy
  have hmain := lcOf_pairing_frame_chart (I := I) hLC (fun _ : ℝ => g) hW x₀ hsrc 0 i j
  simpa using hmain

end Work.Diff.STE.deTurck
