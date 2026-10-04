/-
# Setup data for the `d = 2` branch: the diameter pair and the cap radii

This module records, in the context of the dimension-2 smooth sphere theorem, the standard
packaging of

* Klingenberg's diameter estimate (`π/2 < d(p,q) < π` for a diameter pair),
* the uniqueness of the farthest point (`Submission.GSStep1.step1_diameter_unique_of_lt_pi`),
* finiteness of all Riemannian distances.

Everything here is a direct adaptation of `Submission.Klingenberg.sphere_theorem_of_metric` /
`sphere_theorem_of_klingenberg` to the dimension-2 setting.
-/
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Final.Sphere
import Submission.PinchUniform
import Submission.CurvatureVec
import Submission.Curvature

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.CurvatureVec

namespace Work.Diff.Dim2

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- **The diameter pair of a quarter-pinched surface.** -/
theorem dim2_diam_pair
    (hdim2 : Module.finrank ℝ E = 2)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov) :
    ∃ (g' : RiemannianMetric (fun x : M ↦ TangentSpace I x)),
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'⟩
       IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) ∧
       IsMetricCompatible cov ∧ QuarterPinched cov ∧
       ∃ (p q : M) (D : ℝ),
         Manifold.riemannianEDist I p q = ENNReal.ofReal D ∧
         Real.pi / 2 < D ∧ D < Real.pi ∧
         (∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D) ∧
         (∀ y : M, y ≠ q → Manifold.riemannianEDist I p y < ENNReal.ofReal D) ∧
         (∀ r s : M, Manifold.riemannianEDist I r s ≠ ⊤)) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  haveI : Nonempty M := PathConnectedSpace.nonempty
  have hdim : 2 ≤ Module.finrank ℝ E := by omega
  set g₀ : RiemannianMetric (fun x : M ↦ TangentSpace I x) :=
    (inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g with hg₀def
  -- a uniform strict lower bound for the sectional curvature
  obtain ⟨c, hc1, hlt⟩ :=
    Submission.PinchUniform.exists_uniform_lt_curvVec (I := I) (cov := cov) hmet hpinch htor
  have hcpos : 0 < c := lt_trans zero_lt_one hc1
  have hup4 : ∀ (p : M) (u v : TangentSpace I p), g₀.inner p u u = 1 → g₀.inner p v v = 1 →
      g₀.inner p u v = 0 → g₀.inner p (curvVec cov p u v v) u ≤ 4 :=
    fun p u v hu hv huv =>
      Submission.MetricScale.quarterPinched_pointwise_le (I := I) (cov := cov) hpinch p u v hu hv huv
  -- the scaled metric, with curvature in `(1, 4/c]`
  obtain ⟨g', hinner⟩ :=
    Commons.Geometry.Manifold.Riemannian.exists_scaleMetric
      (E := fun x : M ↦ TangentSpace I x) g₀ hcpos
  have hsmooth₀ : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀⟩
      IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    (inferInstance : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀⟩
      IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x))
  have hsmooth' : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'⟩
      IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Commons.Geometry.Manifold.Riemannian.isContMDiffRiemannianBundle_scaleMetric
      (IB := I) (B := M) (F := E) (E := fun x : M ↦ TangentSpace I x) g₀ g' hcpos hinner hsmooth₀
  have hmetFor' : Submission.MetricScale.IsMetricCompatibleFor g' cov :=
    Submission.MetricScale.isMetricCompatibleFor_scale (I := I) (cov := cov)
      ((Submission.MetricScale.isMetricCompatibleFor_iff (I := I) (cov := cov)).mp hmet) hcpos g' hinner
  have hpinchFor' : Submission.MetricScale.QuarterPinchedFor g' cov :=
    Submission.MetricScale.quarterPinchedFor_scale (I := I) (cov := cov) hc1 g' hinner hpinch hlt
  have hsec' : ∀ (p : M) (u v : TangentSpace I p), g'.inner p u u = 1 → g'.inner p v v = 1 →
      g'.inner p u v = 0 → g'.inner p (curvVec cov p u v v) u ≤ 4 / c :=
    Submission.MetricScale.scaled_sec_le (I := I) (cov := cov) hc1 g' hinner hup4
  -- everything relative to `g'`
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := hsmooth'
  have hmetI : IsMetricCompatible cov :=
    (Submission.MetricScale.isMetricCompatibleFor_iff (I := I) (cov := cov)).mpr hmetFor'
  have hpinchI : QuarterPinched cov :=
    (Submission.MetricScale.quarterPinchedFor_iff (I := I) (cov := cov)).mpr hpinchFor'
  have hge' : ∀ (p : M) (u v : TangentSpace I p), g'.inner p u u = 1 → g'.inner p v v = 1 →
      g'.inner p u v = 0 → (1 : ℝ) ≤ g'.inner p (curvVec cov p u v v) u :=
    fun p u v hu hv huv =>
      (Submission.MetricScale.quarterPinchedFor_pointwise (I := I) (cov := cov)
        hpinchFor' p u v hu hv huv).1.le
  have hlt4' : ∀ (p : M) (u v : TangentSpace I p), g'.inner p u u = 1 → g'.inner p v v = 1 →
      g'.inner p u v = 0 → g'.inner p (curvVec cov p u v v) u < (4 : ℝ) :=
    fun p u v hu hv huv =>
      lt_of_le_of_lt (hsec' p u v hu hv huv) (by rw [div_lt_iff₀ hcpos]; linarith)
  obtain ⟨p₀, q₀, hlower⟩ :=
    Work.Final.klingenbergBound_proved (I := I) (M := M) cov g' hsmooth' hmetFor' htor hge' hlt4'
  obtain ⟨p, q, hdiam⟩ := Submission.Klingenberg.exists_diam_pair (I := I) (M := M)
  have hpq₀ : Manifold.riemannianEDist I p₀ q₀ ≤ Manifold.riemannianEDist I p q := hdiam p₀ q₀
  have hltπ : Manifold.riemannianEDist I p q < ENNReal.ofReal Real.pi :=
    Submission.GlobalBM.riemannianEDist_lt_pi (I := I) (cov := cov) hmetI htor hpinchI hdim p q
  have hfin : Manifold.riemannianEDist I p q ≠ ⊤ :=
    (lt_of_lt_of_le hltπ ENNReal.ofReal_lt_top.le).ne
  set D : ℝ := (Manifold.riemannianEDist I p q).toReal with hDdef
  have hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D := (ENNReal.ofReal_toReal hfin).symm
  have hDgt : Real.pi / 2 < D := by
    have h3 : ENNReal.ofReal (Real.pi / 2) < ENNReal.ofReal D :=
      lt_of_lt_of_le (lt_of_lt_of_le hlower hpq₀) (le_of_eq hpq)
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp h3).1
  have hDlt : D < Real.pi := by
    have h3 : ENNReal.ofReal D < ENNReal.ofReal Real.pi := by rw [← hpq]; exact hltπ
    exact (ENNReal.ofReal_lt_ofReal_iff Real.pi_pos).mp h3
  have hdiamD : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D :=
    fun r s => le_trans (hdiam r s) (le_of_eq hpq)
  refine ⟨g', hsmooth', hmetI, hpinchI, p, q, D, hpq, hDgt, hDlt, ?_, ?_, ?_⟩
  · exact hdiamD
  · intro y hy
    by_contra hcon
    have hyD : Manifold.riemannianEDist I p y = ENNReal.ofReal D := by
      rw [not_lt] at hcon
      exact le_antisymm (le_trans (hdiam p y) (le_of_eq hpq)) hcon
    exact (Submission.GSStep1.step1_diameter_unique_of_lt_pi (I := I) (cov := cov) hmetI htor
      hpinchI hdiamD hDgt hDlt hpq hyD (Ne.symm hy)).elim
  · intro r s
    exact (lt_of_le_of_lt (hdiamD r s) ENNReal.ofReal_lt_top).ne

end

end Work.Diff.Dim2
