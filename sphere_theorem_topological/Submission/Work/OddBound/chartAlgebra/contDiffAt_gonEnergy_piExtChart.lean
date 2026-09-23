import Mathlib
import Submission.Work.OddBound.PiExtChart
import Submission.Work.OddBound.sqDistChart.sqDist_contDiffAt_charts
import Submission.Work.OddBound.polygon.isCritical_gonEnergy_geodesic
import Submission.Work.OddBound.LiftKit

/-!
# Smoothness of the polygon energy in the product extended chart

`gonEnergy p w = (N/2) · Σ_{i<N} d(v_i, v_{i+1})²` is a sum of squared Riemannian distances
between consecutive vertices of the closed polygon through `p` and `w`.  On the region where every
side is shorter than the injectivity radius `R`, the squared distance between two points is `C²` in
each of the two arguments *with respect to the extended charts at those very points*
(`Work.OddBound.sqDistChart.sqDist_contDiffAt_charts`).  Composing with the product extended chart
`piExtChart x` -- whose `j`-th component at `u` is `(extChartAt I (x j)).symm (u j)` -- turns
`gonEnergy` into a sum of such expressions, hence into a `C²` function of `u`; this is the present
lemma.

The proof splits the `Fin N`-indexed sum into its three geometrical shapes: the first side
`d(p, w 0)`, the interior sides `d(w j, w (j+1))`, and the last side `d(w (N-2), p)`; in each case
the pair of vertices is an affine (linear + constant) function of `u` and the generic composition
lemma `contDiffAt_riemannianDist_sq_chart_pair` applies.
-/

namespace Work.OddBound.chartAlgebra

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

section Helpers

set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- **Composition of `sqDist_contDiffAt_charts` with an affine reparametrisation.**  If `a` and `b`
are closer than the injectivity radius `R` (at `a`), then the squared distance between the points
with chart coordinates `(φ u).1` in the chart at `a` and `(φ u).2` in the chart at `b` is a `C²`
function of `u`, at any `u₀` whose image under `φ` is the chart-coordinate pair of `(a, b)`. -/
lemma contDiffAt_riemannianDist_sq_chart_pair
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {R : ℝ} (hR : 0 < R)
    (hinj : ∀ z : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet z R)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : M} {u₀ : F} {φ : F → E × E}
    (hab : Submission.Distance.riemannianDist (I := I) a b < R)
    (hφ : ContDiffAt ℝ 2 φ u₀)
    (hφ0 : φ u₀ = ((extChartAt I a) a, (extChartAt I b) b)) :
    ContDiffAt ℝ 2
      (fun u : F => (Submission.Distance.riemannianDist (I := I)
        ((extChartAt I a).symm (φ u).1) ((extChartAt I b).symm (φ u).2)) ^ 2) u₀ := by
  obtain ⟨w, hw, hwed⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
      (I := I) (cov := cov) hmet htor a b
  have hwn : ‖w‖ = Submission.Distance.riemannianDist (I := I) a b := by
    have h1 := Work.OddBound.polygonValue.edist_eq_ofReal_riemannianDist (I := I) a b
    rw [h1] at hwed
    exact ((ENNReal.ofReal_eq_ofReal_iff (Submission.Distance.riemannianDist_nonneg (I := I) a b)
      (norm_nonneg w)).mp hwed).symm
  have hbase := Work.OddBound.sqDistChart.sqDist_contDiffAt_charts (I := I) (cov := cov) hmet htor
    hR (hinj a) hab hw hwn
  have hbase' : ContDiffAt ℝ 2
      (fun uv : E × E => (Submission.Distance.riemannianDist (I := I)
        ((extChartAt I a).symm uv.1) ((extChartAt I b).symm uv.2)) ^ 2) (φ u₀) := by
    rw [hφ0]; exact hbase
  exact ContDiffAt.comp u₀ hbase' hφ

/-- The last vertex `N-1` of the polygon: `gonVert p w (N-1) = w (N-2)`. -/
lemma gonVert_last (p : M) {N : ℕ} (w : Fin (N-1) → M) (h : N - 2 < N - 1) :
    Work.OddBound.gonVert p w (N-1) = w ⟨N-2, h⟩ := by
  have hh := Work.OddBound.gonVert_succ p w (i := N - 2) h
  rw [show (N - 2) + 1 = N - 1 from by omega] at hh
  exact hh

/-- A positive vertex index `k` below `N` gives the vertex `w (k-1)`. -/
lemma gonVert_pred (p : M) {N : ℕ} (w : Fin (N-1) → M) {k : ℕ}
    (h : k - 1 < N - 1) (hk : 0 < k) :
    Work.OddBound.gonVert p w k = w ⟨k - 1, h⟩ := by
  conv_lhs => rw [show k = (k - 1) + 1 from by omega]
  exact Work.OddBound.gonVert_succ p w (i := k - 1) h

/-- The components of the product extended chart: `(piExtChart x).symm u j` is the `j`-th vertex
in the extended chart at `x j`. -/
lemma piExtChart_symm_apply {N : ℕ} (x : Fin (N-1) → M) (u : Fin (N-1) → E) (j : Fin (N-1)) :
    (Work.OddBound.piExtChart (I := I) x).symm u j = (extChartAt I (x j)).symm (u j) := by
  unfold Work.OddBound.piExtChart
  rw [OpenPartialHomeomorph.pi_symm_apply, extChartAt_coe_symm]; rfl

/-- The polygon `x` itself, in its own product extended chart. -/
lemma piExtChart_apply_self {N : ℕ} (x : Fin (N-1) → M) (j : Fin (N-1)) :
    Work.OddBound.piExtChart (I := I) x x j = (extChartAt I (x j)) (x j) := by
  unfold Work.OddBound.piExtChart
  rw [OpenPartialHomeomorph.pi_apply, Work.OddBound.extChartHomeo_coe, extChartAt_coe]
  rfl

end Helpers

theorem contDiffAt_gonEnergy_piExtChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {N : ℕ} (hN : 3 ≤ N) {p : M} {x : Fin (N - 1) → M}
    {R : ℝ} (hR : 0 < R)
    (hinj : ∀ z : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet z R)
    (hsmall : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p x i < R) :
    ContDiffAt ℝ 2
      (fun u : (Fin (N - 1)) → E =>
        Work.OddBound.gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      ((Work.OddBound.piExtChart (I := I) x) x) := by
  have hterm : ∀ i : Fin N, ContDiffAt ℝ 2
      (fun u : (Fin (N - 1)) → E =>
        (Work.OddBound.gonSideLen (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u) i) ^ 2)
      ((Work.OddBound.piExtChart (I := I) x) x) := by
    intro i
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · -- first side: `d (p, w 0)`
      have hN1 : 0 < N - 1 := by omega
      have hab : Submission.Distance.riemannianDist (I := I) p (x ⟨0, hN1⟩) < R := by
        have h := hsmall i
        dsimp only [Work.OddBound.gonSideLen] at h
        rw [show (i : ℕ) = 0 from h0] at h
        rw [Work.OddBound.gonVert_zero] at h
        rw [Work.OddBound.gonVert_succ (p := p) (w := x) (i := 0) hN1] at h
        simpa using h
      have hside : (fun u : (Fin (N - 1)) → E =>
            (Work.OddBound.gonSideLen (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u) i) ^ 2)
          = fun u : (Fin (N - 1)) → E =>
            (Submission.Distance.riemannianDist (I := I) ((extChartAt I p).symm ((extChartAt I p) p))
              ((extChartAt I (x ⟨0, hN1⟩)).symm (u ⟨0, hN1⟩))) ^ 2 := by
        funext u
        dsimp only [Work.OddBound.gonSideLen]
        rw [show (i : ℕ) = 0 from h0]
        rw [Work.OddBound.gonVert_zero]
        rw [Work.OddBound.gonVert_succ (p := p)
          (w := (Work.OddBound.piExtChart (I := I) x).symm u) (i := 0) hN1]
        rw [piExtChart_symm_apply (I := I) x u, extChartAt_to_inv]
      rw [hside]
      exact contDiffAt_riemannianDist_sq_chart_pair (I := I) (cov := cov) hmet htor hR hinj hab
        (φ := fun u : (Fin (N - 1)) → E => ((extChartAt I p) p, u ⟨0, hN1⟩))
        (contDiffAt_const.prodMk (((ContinuousLinearMap.proj (⟨0, hN1⟩ : Fin (N - 1)) :
          (Fin (N - 1) → E) →L[ℝ] E).contDiff).contDiffAt))
        (by simp [piExtChart_apply_self])
    · rcases lt_or_eq_of_le (show i.val ≤ N - 1 from by omega) with hlt | hlast
      · -- interior side: `d (w j, w (j+1))`
        have hpredlt : i.val - 1 < N - 1 := by omega
        have hab : Submission.Distance.riemannianDist (I := I) (x ⟨i.val - 1, hpredlt⟩)
            (x ⟨i.val, hlt⟩) < R := by
          have h := hsmall i
          dsimp only [Work.OddBound.gonSideLen] at h
          rw [gonVert_pred p x hpredlt hpos] at h
          rw [Work.OddBound.gonVert_succ (p := p) (w := x) (i := i.val) hlt] at h
          simpa using h
        have hside : (fun u : (Fin (N - 1)) → E =>
              (Work.OddBound.gonSideLen (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u) i) ^ 2)
            = fun u : (Fin (N - 1)) → E =>
              (Submission.Distance.riemannianDist (I := I)
                ((extChartAt I (x ⟨i.val - 1, hpredlt⟩)).symm (u ⟨i.val - 1, hpredlt⟩))
                ((extChartAt I (x ⟨i.val, hlt⟩)).symm (u ⟨i.val, hlt⟩))) ^ 2 := by
          funext u
          dsimp only [Work.OddBound.gonSideLen]
          rw [gonVert_pred p ((Work.OddBound.piExtChart (I := I) x).symm u) hpredlt hpos]
          rw [Work.OddBound.gonVert_succ (p := p)
            (w := (Work.OddBound.piExtChart (I := I) x).symm u) (i := i.val) hlt]
          rw [piExtChart_symm_apply (I := I) x u, piExtChart_symm_apply (I := I) x u]
        rw [hside]
        exact contDiffAt_riemannianDist_sq_chart_pair (I := I) (cov := cov) hmet htor hR hinj hab
          (φ := fun u : (Fin (N - 1)) → E => (u ⟨i.val - 1, hpredlt⟩, u ⟨i.val, hlt⟩))
          ((((ContinuousLinearMap.proj (⟨i.val - 1, hpredlt⟩ : Fin (N - 1)) :
              (Fin (N - 1) → E) →L[ℝ] E).contDiff).prodMk
            ((ContinuousLinearMap.proj (⟨i.val, hlt⟩ : Fin (N - 1)) :
              (Fin (N - 1) → E) →L[ℝ] E).contDiff)).contDiffAt)
          (by simp [piExtChart_apply_self])
      · -- last side: `d (w (N-2), p)`
        have hN2 : N - 2 < N - 1 := by omega
        have hab : Submission.Distance.riemannianDist (I := I) (x ⟨N - 2, hN2⟩) p < R := by
          have h := hsmall i
          dsimp only [Work.OddBound.gonSideLen] at h
          rw [show (i : ℕ) = N - 1 from hlast] at h
          rw [gonVert_last p x hN2] at h
          rw [Work.OddBound.gonVert_of_le (p := p) (w := x) (i := (N - 1) + 1)
            (by omega : N ≤ (N - 1) + 1)] at h
          simpa using h
        have hside : (fun u : (Fin (N - 1)) → E =>
              (Work.OddBound.gonSideLen (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u) i) ^ 2)
            = fun u : (Fin (N - 1)) → E =>
              (Submission.Distance.riemannianDist (I := I)
                ((extChartAt I (x ⟨N - 2, hN2⟩)).symm (u ⟨N - 2, hN2⟩))
                ((extChartAt I p).symm ((extChartAt I p) p))) ^ 2 := by
          funext u
          dsimp only [Work.OddBound.gonSideLen]
          rw [show (i : ℕ) = N - 1 from hlast]
          rw [gonVert_last p ((Work.OddBound.piExtChart (I := I) x).symm u) hN2]
          rw [Work.OddBound.gonVert_of_le (p := p)
            (w := (Work.OddBound.piExtChart (I := I) x).symm u) (i := (N - 1) + 1)
            (by omega : N ≤ (N - 1) + 1)]
          rw [piExtChart_symm_apply (I := I) x u, extChartAt_to_inv]
        rw [hside]
        exact contDiffAt_riemannianDist_sq_chart_pair (I := I) (cov := cov) hmet htor hR hinj hab
          (φ := fun u : (Fin (N - 1)) → E => (u ⟨N - 2, hN2⟩, (extChartAt I p) p))
          ((((ContinuousLinearMap.proj (⟨N - 2, hN2⟩ : Fin (N - 1)) :
              (Fin (N - 1) → E) →L[ℝ] E).contDiff).prodMk contDiff_const).contDiffAt)
          (by simp [piExtChart_apply_self])
  have hsum : ContDiffAt ℝ 2
      (fun u : (Fin (N - 1)) → E =>
        ∑ i : Fin N, (Work.OddBound.gonSideLen (I := I) p
          ((Work.OddBound.piExtChart (I := I) x).symm u) i) ^ 2)
      ((Work.OddBound.piExtChart (I := I) x) x) :=
    ContDiffAt.sum (fun i _ => hterm i)
  have hres : ContDiffAt ℝ 2
      (fun u : (Fin (N - 1)) → E => (N : ℝ) / 2 * ∑ i : Fin N, (Work.OddBound.gonSideLen (I := I) p
        ((Work.OddBound.piExtChart (I := I) x).symm u) i) ^ 2)
      ((Work.OddBound.piExtChart (I := I) x) x) :=
    (contDiffAt_const (c := (N : ℝ) / 2)).mul hsum
  simpa only [Work.OddBound.gonEnergy] using hres

end Work.OddBound.chartAlgebra
