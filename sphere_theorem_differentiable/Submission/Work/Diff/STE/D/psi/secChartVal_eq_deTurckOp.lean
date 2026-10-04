import Mathlib
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.D.deTurckCLM
import Submission.Work.Diff.STE.deTurck.chartLieMat_eq_lieJet
import Submission.Work.Diff.EXT.chartRic_mat_smooth_of_jet
import Submission.Work.Diff.EXT.chartRicMat_ricPhi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart expression `secChartVal` of the DeTurck operator is the DeTurck operator

This module closes the C1 bridge of Layer D at the level of *sections*: the explicit chart
expression `Work.Diff.STE.D.secChartVal` of the DeTurck operator (the jet-level operator `pPhi`
contracted with the coordinates of the two tangent vectors in the trivialisation of the tangent
bundle at the chart centre) is, at every point `x` of the chart, equal to the geometric DeTurck
operator `Work.Diff.STE.DeTurck.deTurckOp g g₀ x`.

The proof has three ingredients.

* The jet-level operator and the chart matrix of the geometric operator agree:
  `pPhiJet g g₀ x₀ y = chartDeTurckMat g g₀ x₀ y` for `y ∈ (extChartAt I x₀).target`.  This is the
  definitional decomposition `P = -2 Ric + L_{W}g` together with the two bridges
  `chartRicMat = ricPhi (jet)` (`Work.Diff.EXT.chartRicMat_ricPhi`) and
  `chartLieMat = lieJet` (`Work.Diff.STE.deTurck.chartLieMat_eq_lieJet`), which are the
  manifold-level forms of the coordinate formulas for the Ricci tensor and for the Lie derivative.
* The coordinates `coordCLM x₀ x j` of a tangent vector in the trivialisation at `x₀` are the
  coordinates of that vector in the coordinate frame `cFrame x₀ j`; equivalently
  `u = Σ_j (coordCLM x₀ x j u) • cFrame x₀ j x`.
* The DeTurck operator is bilinear (`Work.Diff.STE.D.deTurckCLM`), so it can be expanded in that
  frame.
-/

namespace Work.Diff.STE.D.psi

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]

noncomputable section

/-! ## 1. The jet-level DeTurck operator is the chart matrix of the geometric DeTurck operator -/

/-- **`pPhiJet` is `chartDeTurckMat`.**  The jet-level DeTurck operator `pPhi`, evaluated on the
spatial `2`-jets of the chart matrices of the background `gbar` and of the metric `g`, is the chart
matrix of the geometric DeTurck operator `deTurckOp g gbar`.  This is `P = -2 Ric + L_{W}g` together
with the EXT bridge `chartRicMat = ricPhi (jet)` and the Lie-derivative bridge
`chartLieMat = lieJet`. -/
lemma pPhiJet_eq_chartDeTurckMat (g gbar : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.STE.DeTurck.pPhiJet (I := I) (M := M) g gbar x₀ y
      = Work.Diff.STE.DeTurck.chartDeTurckMat (I := I) (M := M) g gbar x₀ y := by
  ext i j
  rw [Work.Diff.STE.DeTurck.pPhiJet_apply, Work.Diff.STE.DeTurck.chartDeTurckMat_eq,
    Work.Diff.EXT.chartRicMat_ricPhi x₀ g y hy,
    Work.Diff.STE.deTurck.chartLieMat_eq_lieJet g gbar x₀ y hy]
  rfl

/-! ## 2. The coordinates of a tangent vector in the trivialisation at the chart centre -/

/-- **The coordinate expansion of a tangent vector in the coordinate frame of the chart.**
For `x` in the chart source and `u ∈ TₓM`, the coordinates `coordCLM x₀ x j u` of `u` in the
trivialisation of the tangent bundle at `x₀` are the coefficients of `u` in the coordinate frame
`cFrame x₀ · x`.  Equivalently, `u` is the frame combination with those coefficients. -/
lemma self_eq_sum_coordCLM_smul_cFrame (x₀ : M) {x : M}
    (hx : x ∈ (chartAt H x₀).source) (u : TangentSpace I x) :
    u = ∑ j : Fin (Module.finrank ℝ E),
        coordCLM (I := I) (M := M) x₀ x j u
          • Work.Diff.GE.cFrame (I := I) x₀ j x := by
  have hbase : (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (I := I) x₀
  have hxe : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [hbase]; exact hx
  have h1 : u = (trivializationAt E (TangentSpace I) x₀).symmL ℝ x
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x u) :=
    (Bundle.Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (trivializationAt E (TangentSpace I) x₀) hxe u).symm
  have h2 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x u
      = ∑ j, (Work.Diff.EXT.bB (E := E)).coord j
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x u)
          • (Work.Diff.EXT.bB (E := E)) j := by
    rw [← Module.Basis.sum_repr (Work.Diff.EXT.bB (E := E))
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x u)]
    simp [Module.Basis.coord_apply]
  calc u = (trivializationAt E (TangentSpace I) x₀).symmL ℝ x
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x u) := h1
    _ = (trivializationAt E (TangentSpace I) x₀).symmL ℝ x
        (∑ j, (Work.Diff.EXT.bB (E := E)).coord j
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x u)
          • (Work.Diff.EXT.bB (E := E)) j) := by conv_lhs => rw [h2]
    _ = ∑ j, coordCLM (I := I) (M := M) x₀ x j u
          • Work.Diff.GE.cFrame (I := I) x₀ j x := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_smul, coordCLM_apply, chartCoordOf,
        Work.Diff.GE.cFrame_apply, Submission.Geodesic.frameVector, Work.Diff.EXT.bB,
        Work.Diff.GE.cBasis]

/-! ## 3. The DeTurck operator expanded in the coordinate frame -/

/-- **The DeTurck operator in the coordinate frame.**  Since `deTurckOp g g₀ x` is bilinear
(`Work.Diff.STE.D.deTurckCLM`) and `u`, `v` are frame combinations in the coordinate frame of the
chart at `x₀` (Section 2), the value of the DeTurck operator is the double sum of its frame values
weighted by the coordinates of `u` and `v` in the trivialisation at `x₀`. -/
lemma deTurckOp_sum_cFrame (hLC : Submission.Diff.LCSmooth I M) (g g₀ : Submission.Diff.SMet I M)
    (x₀ : M) {x : M} (hx : x ∈ (chartAt H x₀).source) (u v : TangentSpace I x) :
    ∑ j, ∑ k, Work.Diff.STE.DeTurck.deTurckOp g g₀ x
        (Work.Diff.GE.cFrame (I := I) x₀ j x) (Work.Diff.GE.cFrame (I := I) x₀ k x)
      * (coordCLM (I := I) (M := M) x₀ x j u * coordCLM (I := I) (M := M) x₀ x k v)
      = Work.Diff.STE.DeTurck.deTurckOp g g₀ x u v := by
  obtain ⟨B, hB⟩ := Work.Diff.STE.D.deTurckCLM (I := I) (M := M) hLC g g₀ x
  have hu : u = ∑ j, coordCLM (I := I) (M := M) x₀ x j u
      • Work.Diff.GE.cFrame (I := I) x₀ j x :=
    self_eq_sum_coordCLM_smul_cFrame (I := I) (M := M) x₀ hx u
  have hv : v = ∑ k, coordCLM (I := I) (M := M) x₀ x k v
      • Work.Diff.GE.cFrame (I := I) x₀ k x :=
    self_eq_sum_coordCLM_smul_cFrame (I := I) (M := M) x₀ hx v
  -- the expansion of the bilinear form `B` in the coordinate frame
  have key : ∀ (a b : Fin (Module.finrank ℝ E) → ℝ),
      (∑ j, ∑ k, (a j * b k) * B (Work.Diff.GE.cFrame (I := I) x₀ j x)
          (Work.Diff.GE.cFrame (I := I) x₀ k x))
        = B (∑ j, a j • Work.Diff.GE.cFrame (I := I) x₀ j x)
            (∑ k, b k • Work.Diff.GE.cFrame (I := I) x₀ k x) := by
    intro a b
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  calc ∑ j, ∑ k, Work.Diff.STE.DeTurck.deTurckOp g g₀ x
          (Work.Diff.GE.cFrame (I := I) x₀ j x) (Work.Diff.GE.cFrame (I := I) x₀ k x)
        * (coordCLM (I := I) (M := M) x₀ x j u * coordCLM (I := I) (M := M) x₀ x k v)
      = ∑ j, ∑ k, (coordCLM (I := I) (M := M) x₀ x j u
            * coordCLM (I := I) (M := M) x₀ x k v)
          * B (Work.Diff.GE.cFrame (I := I) x₀ j x)
              (Work.Diff.GE.cFrame (I := I) x₀ k x) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [← hB (Work.Diff.GE.cFrame (I := I) x₀ j x)
          (Work.Diff.GE.cFrame (I := I) x₀ k x)]
        ring
    _ = B (∑ j, coordCLM (I := I) (M := M) x₀ x j u • Work.Diff.GE.cFrame (I := I) x₀ j x)
          (∑ k, coordCLM (I := I) (M := M) x₀ x k v
            • Work.Diff.GE.cFrame (I := I) x₀ k x) :=
        key (fun j => coordCLM (I := I) (M := M) x₀ x j u)
          (fun k => coordCLM (I := I) (M := M) x₀ x k v)
    _ = B u v := by rw [← hu, ← hv]
    _ = Work.Diff.STE.DeTurck.deTurckOp g g₀ x u v := hB u v

/-! ## 5. The bridge -/

/-- **The chart expression of the DeTurck operator is the DeTurck operator.**  The explicit chart
expression `secChartVal` (the jet-level operator `pPhi` contracted with the coordinates of `u` and
`v` in the trivialisation of the tangent bundle at `x₀`) coincides, at every point `x` of the chart
at `x₀`, with the geometric DeTurck operator `deTurckOp g g₀`. -/
theorem secChartVal_eq_deTurckOp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    (hLC : Submission.Diff.LCSmooth I M)
    (g g₀ : Submission.Diff.SMet I M) (x₀ : M) {x : M}
    (hx : x ∈ (chartAt H x₀).source) (u v : TangentSpace I x) :
    Work.Diff.STE.D.secChartVal (I := I) (M := M) g₀ g.inner x₀ x u v
      = Work.Diff.STE.DeTurck.deTurckOp g g₀ x u v := by
  have hxsrc : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hy : (extChartAt I x₀) x ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hxsrc
  have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) x) = x :=
    (extChartAt I x₀).left_inv hxsrc
  calc Work.Diff.STE.D.secChartVal (I := I) (M := M) g₀ g.inner x₀ x u v
      = ∑ j, ∑ k, Work.Diff.STE.DeTurck.pPhiJet (I := I) (M := M) g g₀ x₀
            ((extChartAt I x₀) x) j k
          * (coordCLM (I := I) (M := M) x₀ x j u
              * coordCLM (I := I) (M := M) x₀ x k v) := rfl
    _ = ∑ j, ∑ k, Work.Diff.STE.DeTurck.chartDeTurckMat (I := I) (M := M) g g₀ x₀
            ((extChartAt I x₀) x) j k
          * (coordCLM (I := I) (M := M) x₀ x j u
              * coordCLM (I := I) (M := M) x₀ x k v) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [pPhiJet_eq_chartDeTurckMat g g₀ x₀ hy]
    _ = ∑ j, ∑ k, Work.Diff.STE.DeTurck.deTurckOp g g₀ x
            (Work.Diff.GE.cFrame (I := I) x₀ j x) (Work.Diff.GE.cFrame (I := I) x₀ k x)
          * (coordCLM (I := I) (M := M) x₀ x j u
              * coordCLM (I := I) (M := M) x₀ x k v) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Work.Diff.STE.DeTurck.chartDeTurckMat_apply, hsymm]
    _ = Work.Diff.STE.DeTurck.deTurckOp g g₀ x u v :=
        deTurckOp_sum_cFrame hLC g g₀ x₀ hx u v

end

end Work.Diff.STE.D.psi
