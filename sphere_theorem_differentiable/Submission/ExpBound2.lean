import Submission.RauchGen
import Submission.ExpBound
import Submission.SecondVar2

set_option backward.isDefEq.respectTransparency.types false

/-!
# The pointwise bound for the differential of the exponential map

This file proves the pointwise Rauch bound for the differential of the exponential map,

`‖v‖ · ‖(d exp_p)_v x‖ ≤ sin ‖v‖ · ‖x‖` for `x ⊥ v` (`‖v‖` the Riemannian norm at `p`),

in the division-free form used by the chordal/Toponogov comparison arguments.  The proof uses the
interval-general Rauch comparison theorem `Submission/RauchGen.lean`:

* given `v` with metric norm `c = ‖v‖ < π/3`, the two-parameter family of geodesics with initial
  velocity `v` (`Submission.Gauss.exists_geodesicVariation`) yields a chart geodesic `(u,w)` of
  metric speed `c` and the Jacobi tensor `(Y,U)` along it with
  `(d exp_p)_v x = frameVector p (exp_p v) ((Y 1) x)` (`Submission.FlowJacobi`);
* the rescaled curve `s ↦ (u (s/c), c⁻¹ w (s/c))` has **unit** metric speed, so the interval version
  of Rauch's theorem applies to its Jacobi tensor `Yr s = Y (s/c) ∘ (c ·)`, `Ur s = c⁻¹ (U (s/c) ∘ (c ·))`;
* the invertibility hypothesis of the `Window` is supplied by `RauchGen.isInvertible_Y_gen`
  (the conjugate radius bound, `π/2` in the unit-speed parametrisation).

## Main results

* `rauch_bound_rescaled` : the bound for the rescaled data;
* `exists_expMap_mfderiv_norm_bound` : the final pointwise bound, with the radius `ρ` controlled
  through the chart-metric bounds `ChartBounds.exists_chartGram_bounds`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch
open Submission.ChartBounds
open Submission.JacobiVec
open Submission.JacobiTensor
open Submission.CurvatureSym
open Submission.Gauss
open Submission.JacobiGen
open Submission.IndexForm
open Submission.ConjPoint
open Submission.SecondVar2
open Submission.FlowJacobi
open Submission.RauchUpper
open Submission.RauchGen

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ExpBound2

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## 0. Scaling lemmas for the chart coefficients -/

/-- Scaling a `smulRight`. -/
lemma smulRight_smul' (f : E →L[ℝ] ℝ) (r : ℝ) (y : E) :
    f.smulRight (r • y) = r • f.smulRight y := by
  ext x
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply]
  rw [smul_comm]

/-- `christoffelLM` is linear in its second (velocity) argument. -/
lemma christoffelLM_smul_mid (x₀ p : M) (r : ℝ) (w : TangentSpace I p) :
    christoffelLM cov x₀ p (r • w) = r • christoffelLM cov x₀ p w := by
  rw [christoffelLM, christoffelLM, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [christoffelEval_smul_right]
  exact smulRight_smul' _ r _

/-- `christoffelLM` is additive in its second (velocity) argument. -/
lemma christoffelLM_add_mid (x₀ p : M) (w w' : TangentSpace I p) :
    christoffelLM cov x₀ p (w + w') = christoffelLM cov x₀ p w + christoffelLM cov x₀ p w' := by
  rw [christoffelLM, christoffelLM, christoffelLM, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [christoffelEval_add_right]
  ext x
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply]
  rw [smul_add]

/-- `chartCurv` is quadratic in its last argument. -/
lemma chartCurv_smul_snd (htor : cov.torsion = 0) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (X : E) (r : ℝ) (Y : E) :
    chartCurv cov x₀ p X (r • Y) = r ^ 2 • chartCurv cov x₀ p X Y := by
  have h1 : dB cov x₀ p X (r • Y) (r • Y) = r ^ 2 • dB cov x₀ p X Y Y := by
    calc dB cov x₀ p X (r • Y) (r • Y)
        = r • dB cov x₀ p X (r • Y) Y :=
          dB_smul_last (x₀ := x₀) (p := p) hp X (r • Y) r Y
      _ = r • dB cov x₀ p X Y (r • Y) := by
          rw [← dB_comm_snd (cov := cov) htor hp X Y (r • Y)]
      _ = r • (r • dB cov x₀ p X Y Y) := by
          rw [dB_smul_last (x₀ := x₀) (p := p) hp X Y r Y]
      _ = r ^ 2 • dB cov x₀ p X Y Y := by rw [smul_smul, pow_two]
  have h2 : dB cov x₀ p (r • Y) (r • Y) X = r ^ 2 • dB cov x₀ p Y Y X := by
    calc dB cov x₀ p (r • Y) (r • Y) X
        = r • dB cov x₀ p Y (r • Y) X := dB_smul_fst (x₀ := x₀) (p := p) r (Y) (r • Y) X
      _ = r • dB cov x₀ p Y X (r • Y) := by
          rw [← dB_comm_snd (cov := cov) htor hp Y X (r • Y)]
      _ = r • (r • dB cov x₀ p Y X Y) := by
          rw [dB_smul_last (x₀ := x₀) (p := p) hp Y X r Y]
      _ = r • (r • dB cov x₀ p Y Y X) := by
          rw [← dB_comm_snd (cov := cov) htor hp Y X Y]
      _ = r ^ 2 • dB cov x₀ p Y Y X := by rw [smul_smul, pow_two]
  have h3 : chrB cov x₀ p (chrB cov x₀ p (r • Y) (r • Y)) X
      = r ^ 2 • chrB cov x₀ p (chrB cov x₀ p Y Y) X := by
    calc chrB cov x₀ p (chrB cov x₀ p (r • Y) (r • Y)) X
        = chrB cov x₀ p (r • chrB cov x₀ p (r • Y) Y) X := by
          rw [chrB_smul_snd (x₀ := x₀) (p := p) (c := r) (a := r • Y) (b := Y)]
      _ = r • chrB cov x₀ p (chrB cov x₀ p (r • Y) Y) X := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r)
            (a := chrB cov x₀ p (r • Y) Y) (b := X) hp]
      _ = r • chrB cov x₀ p (r • chrB cov x₀ p Y Y) X := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r) (a := Y) (b := Y) hp]
      _ = r • (r • chrB cov x₀ p (chrB cov x₀ p Y Y) X) := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r)
            (a := chrB cov x₀ p Y Y) (b := X) hp]
      _ = r ^ 2 • chrB cov x₀ p (chrB cov x₀ p Y Y) X := by rw [smul_smul, pow_two]
  have h4 : chrB cov x₀ p (chrB cov x₀ p (r • Y) X) (r • Y)
      = r ^ 2 • chrB cov x₀ p (chrB cov x₀ p Y X) Y := by
    calc chrB cov x₀ p (chrB cov x₀ p (r • Y) X) (r • Y)
        = r • chrB cov x₀ p (chrB cov x₀ p (r • Y) X) Y := by
          rw [chrB_smul_snd (x₀ := x₀) (p := p) (c := r)
            (a := chrB cov x₀ p (r • Y) X) (b := Y)]
      _ = r • chrB cov x₀ p (r • chrB cov x₀ p Y X) Y := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r) (a := Y) (b := X) hp]
      _ = r • (r • chrB cov x₀ p (chrB cov x₀ p Y X) Y) := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r)
            (a := chrB cov x₀ p Y X) (b := Y) hp]
      _ = r ^ 2 • chrB cov x₀ p (chrB cov x₀ p Y X) Y := by rw [smul_smul, pow_two]
  rw [chartCurv, chartCurv, h1, h2, h3, h4]
  simp only [smul_sub, smul_add]

/-- `gammaOp` is linear in the velocity. -/
lemma gammaOp_scale (x₀ : M) {u w : ℝ → E} {t : ℝ} (r : ℝ) :
    gammaOp (cov := cov) x₀ u (fun s => r • w s) t = r • gammaOp (cov := cov) x₀ u w t := by
  rw [gammaOp, gammaOp, frameVector_smul, christoffelLM_smul_mid]

/-- `curvOp` is quadratic in the velocity. -/
lemma curvOp_smul_mid (htor : cov.torsion = 0) (x₀ : M) {u w : ℝ → E} {t : ℝ} (r : ℝ)
    (htgt : u t ∈ (extChartAt I x₀).target) :
    curvOp (cov := cov) x₀ u (fun s => r • w s) t = r ^ 2 • curvOp (cov := cov) x₀ u w t := by
  have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) htgt
  show (∑ i : Fin (Module.finrank ℝ E),
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
        (chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i)
          (r • w t)))
    = r ^ 2 • (∑ i : Fin (Module.finrank ℝ E),
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
        (chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i) (w t)))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartCurv_smul_snd (cov := cov) htor x₀ hsrc]
  exact smulRight_smul' _ (r ^ 2) _

/-! ## 1. The rescaled unit-speed Jacobi data and Rauch's bound -/

/-- **Rauch's bound for the rescaled (unit-speed) chart geodesic.**  Let `(u,w)` be a chart geodesic
whose metric speed is `c > 0` (so that `s ↦ (u (s/c), c⁻¹ w (s/c))` has unit metric speed) and let
`(Y,U)` be the Jacobi tensor along it with `Y 0 = 0`, `U 0 = 1`.  Then for `x ⊥ v` (in the metric at
the base point) with `c < π/3`,

`⟨(Y 1) x, (Y 1) x⟩ ≤ sin(c)² c⁻² ⟨x,x⟩`.

The hypothesis `c < π/3` only enters through the invertibility of the Jacobi tensor on the window
`(0, 5c/4)` (`RauchGen.isInvertible_Y_gen`, i.e. the conjugate radius bound `π/2`). -/
theorem rauch_bound_rescaled {x₀ : M} {v x : E} {u w : ℝ → E} {Y U : ℝ → E →L[ℝ] E}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hgc : HasChartGeodesic cov x₀ v u w)
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)
        = chartGram (I := I) x₀ x₀ v v)
    {c : ℝ} (hc : 0 < c) (hcsq : c ^ 2 = chartGram (I := I) x₀ x₀ v v)
    (hc3 : c < Real.pi / 3)
    (hY : ∀ t ∈ Icc (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1)
    (horth : chartGram (I := I) x₀ x₀ v x = 0) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 1)) ((Y 1) x) ((Y 1) x)
      ≤ Real.sin c ^ 2 * ((c⁻¹) ^ 2 * chartGram (I := I) x₀ x₀ x x) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  -- the rescaled data
  set ut : ℝ → E := fun s => u (c⁻¹ * s) with hutdef
  set wt : ℝ → E := fun s => c⁻¹ • w (c⁻¹ * s) with hwtdef
  set Yr : ℝ → E →L[ℝ] E := fun s => (Y (c⁻¹ * s)).comp (c • (1 : E →L[ℝ] E)) with hYrdef
  set Ur : ℝ → E →L[ℝ] E := fun s => c⁻¹ • ((U (c⁻¹ * s)).comp (c • (1 : E →L[ℝ] E))) with hUrdef
  have hA' : -(3 * c / 2) < 0 := by linarith
  have hB' : 0 < 3 * c / 2 := by linarith
  -- the rescaled parameter lies in the original intervals
  have hmaps3 : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2), c⁻¹ * s ∈ Ioo (-(3 / 2) : ℝ) (3 / 2) := by
    intro s hs
    have hinv1 : c⁻¹ * (-(3 * c / 2)) = -(3 / 2) := by field_simp
    have hinv2 : c⁻¹ * (3 * c / 2) = 3 / 2 := by field_simp
    have h1 : -(3 / 2 : ℝ) < c⁻¹ * s := by
      calc -(3 / 2 : ℝ) = c⁻¹ * (-(3 * c / 2)) := hinv1.symm
        _ < c⁻¹ * s := mul_lt_mul_of_pos_left hs.1 hcinv
    have h2 : c⁻¹ * s < 3 / 2 := by
      calc c⁻¹ * s < c⁻¹ * (3 * c / 2) := mul_lt_mul_of_pos_left hs.2 hcinv
        _ = 3 / 2 := hinv2
    exact ⟨h1, h2⟩
  have hmaps : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2), c⁻¹ * s ∈ Ioo (-2 : ℝ) 2 :=
    fun s hs => ⟨lt_trans (by norm_num : -(2 : ℝ) < -(3 / 2)) (hmaps3 s hs).1,
      lt_trans (hmaps3 s hs).2 (by norm_num : (3 / 2 : ℝ) < 2)⟩
  have hmapsI : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      c⁻¹ * s ∈ Icc (-(3 / 2) : ℝ) (3 / 2) :=
    fun s hs => ⟨(hmaps3 s hs).1.le, (hmaps3 s hs).2.le⟩
  -- (the two derivative clauses)
  have hgeod : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      HasDerivAt ut (wt s) s := by
    intro s hs
    change HasDerivAt (fun s : ℝ => u (c⁻¹ * s)) (c⁻¹ • w (c⁻¹ * s)) s
    have hφ : HasDerivAt (fun s : ℝ => c⁻¹ * s) c⁻¹ s := by
      simpa using (hasDerivAt_id s).const_mul c⁻¹
    have h := (hgc.2.2.2.1 _ (hmaps s hs)).scomp s hφ
    simpa [Function.comp_def] using h
  have hgeod2 : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      HasDerivAt wt (chartGeodesicVectorField cov x₀ (ut s, wt s)) s := by
    intro s hs
    change HasDerivAt (fun s : ℝ => c⁻¹ • w (c⁻¹ * s))
      (chartGeodesicVectorField cov x₀ (u (c⁻¹ * s), c⁻¹ • w (c⁻¹ * s))) s
    have hφ : HasDerivAt (fun s : ℝ => c⁻¹ * s) c⁻¹ s := by
      simpa using (hasDerivAt_id s).const_mul c⁻¹
    have h1 : HasDerivAt (fun s : ℝ => w (c⁻¹ * s))
        (c⁻¹ • chartGeodesicVectorField cov x₀ (u (c⁻¹ * s), w (c⁻¹ * s))) s := by
      have h := (hgc.2.2.2.2 _ (hmaps s hs)).scomp s hφ
      simpa [Function.comp_def] using h
    have h2 := h1.const_smul c⁻¹
    refine h2.congr_deriv ?_
    rw [chartGeodesicVectorField_smul cov x₀ c⁻¹ (u (c⁻¹ * s), w (c⁻¹ * s))
      (hgc.2.2.1 _ (hmaps s hs)), smul_smul, pow_two]
  -- the rescaled chart geodesic
  have hgeo : HasChartGeodesicOn cov x₀ x₀ (c⁻¹ • v) ut wt (-(3 * c / 2)) (3 * c / 2) := by
    refine ⟨?_, ?_, ?_, hgeod, hgeod2⟩
    · change u (c⁻¹ * 0) = (extChartAt I x₀) x₀
      rw [mul_zero]; exact hgc.1
    · change c⁻¹ • w (c⁻¹ * 0)
        = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ (c⁻¹ • v)
      rw [mul_zero, hgc.2.1, map_smul]
    · intro s hs
      change u (c⁻¹ * s) ∈ (extChartAt I x₀).target
      exact hgc.2.2.1 _ (hmaps s hs)
  -- the unit-speed condition
  have hunit : ∀ t ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (ut t)) (wt t) (wt t) = 1 := by
    intro t ht
    change chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (c⁻¹ * t)))
      (c⁻¹ • w (c⁻¹ * t)) (c⁻¹ • w (c⁻¹ * t)) = 1
    rw [chartGram_smul_fst, chartGram_smul_snd, hspeed _ (hmaps t ht), ← hcsq]
    field_simp
  -- the relations between the rescaled and the original coefficients
  have hΓ : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      gammaOp (cov := cov) x₀ ut wt s = c⁻¹ • gammaOp (cov := cov) x₀ u w (c⁻¹ * s) := by
    intro s hs
    change gammaOp (cov := cov) x₀ (fun s' => u (c⁻¹ * s'))
      (fun s' => c⁻¹ • w (c⁻¹ * s')) s = c⁻¹ • gammaOp (cov := cov) x₀ u w (c⁻¹ * s)
    exact gammaOp_scale (cov := cov) x₀ (u := u) (w := w) (t := c⁻¹ * s) c⁻¹
  have hR : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      curvOp (cov := cov) x₀ ut wt s = (c⁻¹) ^ 2 • curvOp (cov := cov) x₀ u w (c⁻¹ * s) := by
    intro s hs
    change curvOp (cov := cov) x₀ (fun s' => u (c⁻¹ * s'))
      (fun s' => c⁻¹ • w (c⁻¹ * s')) s = (c⁻¹) ^ 2 • curvOp (cov := cov) x₀ u w (c⁻¹ * s)
    exact curvOp_smul_mid (cov := cov) htor x₀ (u := u) (w := w) (t := c⁻¹ * s)
      c⁻¹ (hgc.2.2.1 _ (hmaps s hs))
  -- the Jacobi system of the rescaled curve
  have hYres : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      HasDerivAt Yr (Ur s - (gammaOp (cov := cov) x₀ ut wt s).comp (Yr s)) s := by
    intro s hs
    have hφ : HasDerivAt (fun s : ℝ => c⁻¹ * s) c⁻¹ s := by
      simpa using (hasDerivAt_id s).const_mul c⁻¹
    have h1 := (hY (c⁻¹ * s) (hmapsI s hs)).scomp s hφ
    have h2 := h1.clm_comp (hasDerivAt_const (x := s) (c := (c • (1 : E →L[ℝ] E))))
    simp only [ContinuousLinearMap.comp_zero, add_zero] at h2
    refine h2.congr_deriv ?_
    rw [hUrdef, hYrdef, hΓ s hs]
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_assoc, smul_sub]
  have hUres : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      HasDerivAt Ur (-((gammaOp (cov := cov) x₀ ut wt s).comp (Ur s))
        - (curvOp (cov := cov) x₀ ut wt s).comp (Yr s)) s := by
    intro s hs
    have hφ : HasDerivAt (fun s : ℝ => c⁻¹ * s) c⁻¹ s := by
      simpa using (hasDerivAt_id s).const_mul c⁻¹
    have h1 := (hU (c⁻¹ * s) (hmapsI s hs)).scomp s hφ
    have h2 := h1.clm_comp (hasDerivAt_const (x := s) (c := (c • (1 : E →L[ℝ] E))))
    simp only [ContinuousLinearMap.comp_zero, add_zero] at h2
    have h3 := h2.const_smul c⁻¹
    have h4 : HasDerivAt Ur (c⁻¹ • ((c⁻¹ • (-((gammaOp (cov := cov) x₀ u w (c⁻¹ * s)).comp
        (U (c⁻¹ * s))) - (curvOp (cov := cov) x₀ u w (c⁻¹ * s)).comp (Y (c⁻¹ * s)))).comp
          (c • (1 : E →L[ℝ] E)))) s := by
      rw [hUrdef]
      exact h3
    refine h4.congr_deriv ?_
    rw [hUrdef, hYrdef, hΓ s hs, hR s hs]
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
      map_sub, map_neg, smul_sub, smul_neg, smul_add, map_smul, smul_smul, pow_two]
    module
  -- the Jacobi data
  have hY0' : Yr 0 = 0 := by
    change (Y (c⁻¹ * 0)).comp (c • (1 : E →L[ℝ] E)) = 0
    rw [mul_zero, hY0, ContinuousLinearMap.zero_comp]
  have hU0' : Ur 0 = 1 := by
    change c⁻¹ • ((U (c⁻¹ * 0)).comp (c • (1 : E →L[ℝ] E))) = 1
    rw [mul_zero, hU0]
    have h1c : ((1 : E →L[ℝ] E).comp (c • (1 : E →L[ℝ] E))) = c • (1 : E →L[ℝ] E) := by
      ext x
      simp [ContinuousLinearMap.one_apply]
    rw [h1c, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  -- the `JData`
  let D : JData cov x₀ x₀ (c⁻¹ • v) ut wt (-(3 * c / 2)) (3 * c / 2) :=
    { hA := hA', hB := hB', htor := htor, hmet := hmet, hpinch := hpinch,
      hgeo := ⟨hgeo.1, hgeo.2.1, hgeo.2.2.1, hgeod, hgeod2⟩,
      hunit := hunit, Y := Yr, U := Ur, hY := hYres, hU := hUres,
      hY0 := hY0', hU0 := hU0' }
  have hDY : D.Y = Yr := rfl
  -- the window
  have hYinv : ∀ s ∈ Ioo 0 (5 * c / 4), (D.Y s).IsInvertible := by
    intro s hs
    refine D.isInvertible_Y_gen (by linarith [hs.1])
      (by linarith [hs.2, hc3, Real.pi_pos]) (by linarith [hs.2, hc])
  let W : JData.Window D :=
    { T := 5 * c / 4, hT := by linarith, hTB := by linarith [hc],
      hTpi := by linarith [hc3, Real.pi_pos], hYinv := hYinv }
  -- the orthogonality hypothesis
  have hut0 : ut 0 = (extChartAt I x₀) x₀ := by
    change u (c⁻¹ * 0) = (extChartAt I x₀) x₀
    rw [mul_zero]; exact hgc.1
  have hbase0 : (extChartAt I x₀).symm (ut 0) = x₀ := by
    rw [hut0]
    exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have horth_res : chartGram (I := I) x₀ ((extChartAt I x₀).symm (ut 0)) (c⁻¹ • x) (wt 0) = 0 := by
    change chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (c⁻¹ * 0))) (c⁻¹ • x)
      (c⁻¹ • w (c⁻¹ * 0)) = 0
    rw [mul_zero, hgc.1, (extChartAt I x₀).left_inv (mem_extChartAt_source x₀), hgc.2.1,
      continuousLinearMapAt_trivializationAt_self]
    change chartGram (I := I) x₀ x₀ (c⁻¹ • x) (c⁻¹ • v) = 0
    rw [chartGram_smul_fst, chartGram_smul_snd, chartGram_comm, horth, mul_zero, mul_zero]
  have hmain := D.rauch_upper_gen W (a := c⁻¹ • x) (ht := ⟨hc, by show c < 5 * c / 4; linarith [hc]⟩) horth_res
  -- convert to the original (unrescaled) quantities
  have hutc : ut c = u 1 := by
    change u (c⁻¹ * c) = u 1
    rw [inv_mul_cancel₀ hcne]
  have hYc : D.Y c (c⁻¹ • x) = (Y 1) x := by
    rw [hDY]
    change (Y (c⁻¹ * c)).comp (c • (1 : E →L[ℝ] E)) (c⁻¹ • x) = Y 1 x
    rw [inv_mul_cancel₀ hcne, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, smul_smul, mul_inv_cancel₀ hcne, one_smul]
  have hbase : chartGram (I := I) x₀ ((extChartAt I x₀).symm (ut 0)) (c⁻¹ • x) (c⁻¹ • x)
      = (c⁻¹) ^ 2 * chartGram (I := I) x₀ x₀ x x := by
    rw [hbase0, chartGram_smul_fst, chartGram_smul_snd]
    ring
  rw [hutc, hYc, hbase] at hmain
  exact hmain


/-! ## 2. The pointwise bound for the differential of the exponential map -/

/-- **The pointwise Rauch bound for the differential of the exponential map.**  There is `ρ > 0`
such that for all tangent vectors `v` with (Riemannian) norm `< ρ` at `x₀` and all `x ⊥ v`,

`‖v‖ · ‖(d exp_{x₀})_v x‖ ≤ sin ‖v‖ · ‖x‖`

(with all norms the Riemannian ones). -/
theorem exists_expMap_mfderiv_norm_bound [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v x : E, ‖v‖ < ρ →
      chartGram (I := I) x₀ x₀ v x = 0 →
      Real.sqrt (chartGram (I := I) x₀ x₀ v v)
          * ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
        ≤ Real.sin (Real.sqrt (chartGram (I := I) x₀ x₀ v v))
          * Real.sqrt (chartGram (I := I) x₀ x₀ x x) := by
  obtain ⟨ρ₁, hρ₁, hvar⟩ := Submission.Gauss.exists_geodesicVariation (cov := cov) x₀
  obtain ⟨ρ₂, hρ₂, hsm⟩ := Submission.Geodesic.exists_radius_contMDiffAt_expMap (cov := cov) x₀
  obtain ⟨lam, hlam, Lam, hLam, hgram⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I)
    (x₀ := x₀) (K := {x₀}) isCompact_singleton (singleton_nonempty x₀) (by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact mem_chart_source H x₀)
  refine ⟨min ρ₁ (min ρ₂ (Real.pi / 3 / Real.sqrt Lam)),
    lt_min hρ₁ (lt_min hρ₂ (div_pos (div_pos Real.pi_pos (by norm_num))
      (Real.sqrt_pos.mpr hLam))), ?_⟩
  intro v x hv hvorth
  have hv1 : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < ρ₂ := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hv3 : ‖v‖ < Real.pi / 3 / Real.sqrt Lam :=
    lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  rcases eq_or_ne v 0 with rfl | hv0
  · simp only [chartGram_zero, Real.sqrt_zero, zero_mul, Real.sin_zero]
    norm_num
  set c : ℝ := Real.sqrt (chartGram (I := I) x₀ x₀ v v) with hcdef
  have hlamv := (hgram x₀ (by simp) v).1
  have hLamv := (hgram x₀ (by simp) v).2
  have hcvpos : 0 < chartGram (I := I) x₀ x₀ v v := by
    have hvv : 0 < ‖v‖ ^ 2 := by positivity
    nlinarith [hlamv, hlam, hvv]
  have hcpos : 0 < c := Real.sqrt_pos.mpr hcvpos
  have hcsq : c ^ 2 = chartGram (I := I) x₀ x₀ v v := Real.sq_sqrt hcvpos.le
  have hc_le : c ≤ Real.sqrt Lam * ‖v‖ := by
    have h1 : c ≤ Real.sqrt (Lam * ‖v‖ ^ 2) := by
      rw [hcdef]
      exact Real.sqrt_le_sqrt hLamv
    rwa [Real.sqrt_mul hLam.le, Real.sqrt_sq (norm_nonneg v)] at h1
  have hc3 : c < Real.pi / 3 := by
    calc c ≤ Real.sqrt Lam * ‖v‖ := hc_le
      _ < Real.sqrt Lam * (Real.pi / 3 / Real.sqrt Lam) :=
          mul_lt_mul_of_pos_left hv3 (Real.sqrt_pos.mpr hLam)
      _ = Real.pi / 3 := by field_simp
  change c * ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
    ≤ Real.sin c * Real.sqrt (chartGram (I := I) x₀ x₀ x x)
  -- the two-parameter family of geodesics with velocity `v + t • x`
  obtain ⟨δ, Φ, hδ, hP0, hPv, hODE, hTGT, hSM, hEXP⟩ := hvar v hv1 x
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hgc : HasChartGeodesic cov x₀ v (gc Φ) (gv Φ) :=
    hasChartGeodesic_of_variation (cov := cov) hδ hP0 (by have := hPv 0 h0; simpa using this)
      hTGT hODE
  -- the Jacobi tensor along it
  obtain ⟨Y, U, hY0, hU0, hY', hU'⟩ := exists_jacobiSystem (cov := cov) htor hgc
    (a := -(3 / 2)) (b := 3 / 2) (by norm_num)
    (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩) (by norm_num)
  -- the identification of the differential of `exp` with the Jacobi field
  have hvsm : MDifferentiableAt 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v :=
    (hsm v hv2).mdifferentiableAt (by simp)
  have hdiff : (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x
      = frameVector (I := I) x₀ (expMap cov x₀ v) ((Y 1) x) :=
    mfderiv_expMap_eq_jacobiTensor (cov := cov) htor hδ hP0 hPv hTGT hODE hSM hEXP hvsm
      (fun t ht => hY' t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (fun t ht => hU' t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hY0 hU0
  have hexp1 : expMap cov x₀ v = (extChartAt I x₀).symm ((gc Φ) 1) := by
    have h := hEXP 1 (by norm_num) 0 h0
    simpa using h
  -- the chart speed of the geodesic
  have hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm ((gc Φ) t)) ((gv Φ) t) ((gv Φ) t)
        = chartGram (I := I) x₀ x₀ v v := by
    intro t ht
    rw [Submission.ExpBound.chartGram_self_const_of_hasChartGeodesic hmet hgc t ht,
      ← Submission.ExpBound.chartGram_self_eq_norm_sq]
  -- Rauch's bound for the rescaled (unit-speed) geodesic
  have hrauch := rauch_bound_rescaled (cov := cov) hmet htor hpinch hgc hspeed hcpos hcsq hc3
    hY' hU' hY0 hU0 hvorth
  have hrauch2 : chartGram (I := I) x₀ (expMap cov x₀ v) ((Y 1) x) ((Y 1) x)
      ≤ (Real.sin c * c⁻¹) ^ 2 * chartGram (I := I) x₀ x₀ x x := by
    rw [hexp1]
    refine hrauch.trans (le_of_eq ?_)
    ring
  -- convert to norms
  have hnorm : ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
      = Real.sqrt (chartGram (I := I) x₀ (expMap cov x₀ v) ((Y 1) x) ((Y 1) x)) := by
    rw [hdiff, chartGram_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hsinpos : 0 ≤ Real.sin c * c⁻¹ := by
    refine mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hcpos.le ?_) (inv_pos.mpr hcpos).le
    linarith [hc3, Real.pi_pos]
  have hsqrt := Real.sqrt_le_sqrt hrauch2
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hsinpos] at hsqrt
  rw [← hnorm] at hsqrt
  calc c * ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
      ≤ c * ((Real.sin c * c⁻¹) * Real.sqrt (chartGram (I := I) x₀ x₀ x x)) :=
        mul_le_mul_of_nonneg_left hsqrt hcpos.le
    _ = Real.sin c * Real.sqrt (chartGram (I := I) x₀ x₀ x x) := by
        field_simp


/-- The same bound, with the hypothesis on the **Riemannian** norm of `v` at `x₀` instead of the
ambient norm of `E`. -/
theorem exists_expMap_mfderiv_norm_bound_metric [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v x : E,
      Real.sqrt (chartGram (I := I) x₀ x₀ v v) < ρ →
      chartGram (I := I) x₀ x₀ v x = 0 →
      Real.sqrt (chartGram (I := I) x₀ x₀ v v)
          * ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
        ≤ Real.sin (Real.sqrt (chartGram (I := I) x₀ x₀ v v))
          * Real.sqrt (chartGram (I := I) x₀ x₀ x x) := by
  obtain ⟨ρ, hρ, hb⟩ := exists_expMap_mfderiv_norm_bound (cov := cov) hmet htor hpinch x₀
  obtain ⟨lam, hlam, Lam, hLam, hgram⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I)
    (x₀ := x₀) (K := {x₀}) isCompact_singleton (singleton_nonempty x₀) (by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact mem_chart_source H x₀)
  refine ⟨Real.sqrt lam * ρ, mul_pos (Real.sqrt_pos.mpr hlam) hρ, fun v x hv hvorth => ?_⟩
  refine hb v x ?_ hvorth
  have hle := (hgram x₀ (by simp) v).1
  have h2 : Real.sqrt lam * ‖v‖ ≤ Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul hlam.le]
    exact Real.sqrt_le_sqrt hle
  have h3 : Real.sqrt lam * ‖v‖ < Real.sqrt lam * ρ := lt_of_le_of_lt h2 hv
  exact lt_of_mul_lt_mul_left h3 (Real.sqrt_nonneg lam)


/-- **The flat (chordal) form** for non-vanishing `v`: `‖(d exp_p)_v x‖ ≤ ‖x‖` for `x ⊥ v`. -/
theorem exists_expMap_mfderiv_norm_le_of_ne [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v x : E,
      0 < chartGram (I := I) x₀ x₀ v v →
      Real.sqrt (chartGram (I := I) x₀ x₀ v v) < ρ →
      chartGram (I := I) x₀ x₀ v x = 0 →
      ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
        ≤ Real.sqrt (chartGram (I := I) x₀ x₀ x x) := by
  obtain ⟨ρ, hρ, hb⟩ := exists_expMap_mfderiv_norm_bound_metric (cov := cov) hmet htor hpinch x₀
  refine ⟨ρ, hρ, fun v x hvpos hv hvorth => ?_⟩
  have hcp : 0 < Real.sqrt (chartGram (I := I) x₀ x₀ v v) := Real.sqrt_pos.mpr hvpos
  have hsin : Real.sin (Real.sqrt (chartGram (I := I) x₀ x₀ v v))
      ≤ Real.sqrt (chartGram (I := I) x₀ x₀ v v) := Real.sin_le hcp.le
  have h2 : Real.sqrt (chartGram (I := I) x₀ x₀ v v)
      * ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
      ≤ Real.sqrt (chartGram (I := I) x₀ x₀ v v)
        * Real.sqrt (chartGram (I := I) x₀ x₀ x x) :=
    (hb v x hv hvorth).trans
      (mul_le_mul_of_nonneg_right hsin (Real.sqrt_nonneg _))
  exact le_of_mul_le_mul_left h2 hcp



/-- Bilinearity helpers for `chartGram` in the second slot. -/
lemma chartGram_neg_snd' (x₀ p : M) (a b : E) :
    chartGram (I := I) x₀ p a (-b) = -chartGram (I := I) x₀ p a b := by
  rw [chartGram_comm, chartGram_neg_fst, chartGram_comm]

lemma chartGram_sub_snd' (x₀ p : M) (a b c : E) :
    chartGram (I := I) x₀ p a (b - c)
      = chartGram (I := I) x₀ p a b - chartGram (I := I) x₀ p a c := by
  rw [sub_eq_add_neg, chartGram_add_snd, chartGram_neg_snd']
  ring

/-- **Rauch's bound for the differential of the exponential map, without orthogonality.**  For `v`
of non-zero Riemannian norm and *every* `x : E`,
`‖(d exp_{x₀})_v x‖ ≤ ‖x‖`, with the norms the Riemannian ones (at `exp_{x₀} v` and at `x₀`).

The proof decomposes `x` into the parts parallel and orthogonal to `v`: the parallel part is handled
exactly by Gauss's lemma (`Gauss.gauss_lemma_fderiv`), the orthogonal part by
`exists_expMap_mfderiv_norm_le_of_ne`. -/
theorem mfderiv_expMap_norm_le [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v x : E,
      0 < chartGram (I := I) x₀ x₀ v v →
      Real.sqrt (chartGram (I := I) x₀ x₀ v v) < ρ →
      ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
        ≤ Real.sqrt (chartGram (I := I) x₀ x₀ x x) := by
  obtain ⟨ρf, hρf, hflat⟩ := exists_expMap_mfderiv_norm_le_of_ne (cov := cov) hmet htor hpinch x₀
  obtain ⟨ρg, hρg, hgauss⟩ := Submission.Gauss.gauss_lemma_fderiv (cov := cov) hmet htor x₀
  obtain ⟨ρc, hρc, hchartgeo⟩ := exists_pos_hasChartGeodesic (cov := cov) x₀
  obtain ⟨lam, hlam, Lam, hLam, hgram⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I)
    (x₀ := x₀) (K := {x₀}) isCompact_singleton (singleton_nonempty x₀) (by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact mem_chart_source H x₀)
  have hsqrtlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨min ρf (Real.sqrt lam * min ρg ρc),
    lt_min hρf (mul_pos hsqrtlam (lt_min hρg hρc)), fun v x hvpos hv => ?_⟩
  have hvf : Real.sqrt (chartGram (I := I) x₀ x₀ v v) < ρf :=
    lt_of_lt_of_le hv (min_le_left _ _)
  have hvg : Real.sqrt (chartGram (I := I) x₀ x₀ v v) < Real.sqrt lam * min ρg ρc :=
    lt_of_lt_of_le hv (min_le_right _ _)
  have hvamb : ‖v‖ < min ρg ρc := by
    have hle := (hgram x₀ (by simp) v).1
    have h1 : Real.sqrt lam * ‖v‖ ≤ Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
      rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul hlam.le]
      exact Real.sqrt_le_sqrt hle
    have h2 : Real.sqrt lam * ‖v‖ < Real.sqrt lam * min ρg ρc := lt_of_le_of_lt h1 hvg
    exact lt_of_mul_lt_mul_left h2 (Real.sqrt_nonneg lam)
  have hvρg : ‖v‖ < ρg := lt_of_lt_of_le hvamb (min_le_left _ _)
  have hvρc : ‖v‖ < ρc := lt_of_lt_of_le hvamb (min_le_right _ _)
  -- the manifold point and its membership in the chart
  set p : M := expMap cov x₀ v with hpdef
  have hp_src : p ∈ (chartAt H x₀).source := by
    obtain ⟨u, w, hgc⟩ := hchartgeo v hvρc.le
    have hexp : expMap cov x₀ v = (extChartAt I x₀).symm (u 1) :=
      expMap_eq_of_hasChartGeodesic (cov := cov) hgc
    rw [hpdef, hexp]
    exact mem_source_chartCurve (I := I) (hgc.2.2.1 1 (by norm_num))
  have hp_base : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hp_src
  -- the coordinates of the differential in the chart at `x₀`
  set φ : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
    with hφdef
  set D : E →L[ℝ] E := φ.comp (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) with hDdef
  have hframe : ∀ y : E, frameVector (I := I) x₀ p (D y)
      = (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) y := by
    intro y
    have h1 := Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (e := trivializationAt E (TangentSpace I) x₀) hp_base
      ((mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) y)
    show (Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) p) (D y) = _
    rw [hDdef, ContinuousLinearMap.comp_apply]
    exact h1
  -- Gauss's lemma in coordinates
  have hG : ∀ y : E, chartGram (I := I) x₀ p (D v) (D y) = chartGram (I := I) x₀ x₀ v y := by
    intro y
    rw [chartGram_apply, hframe v, hframe y]
    exact hgauss v hvρg y
  -- the decomposition of `x`
  set α : ℝ := chartGram (I := I) x₀ x₀ v x / chartGram (I := I) x₀ x₀ v v with hαdef
  set xp : E := α • v with hxpdef
  set xo : E := x - xp with hxodef
  have hvvne : chartGram (I := I) x₀ x₀ v v ≠ 0 := ne_of_gt hvpos
  have ho : chartGram (I := I) x₀ x₀ v xo = 0 := by
    rw [hxodef, chartGram_sub_snd', hxpdef, chartGram_smul_snd, hαdef]
    field_simp
    ring
  have hx : x = xp + xo := by rw [hxodef]; abel
  -- the coordinates of the two parts
  have hDp : D xp = α • D v := by rw [hxpdef, map_smul]
  have hDxo : D xo = D x - D xp := by rw [hxodef, map_sub]
  have hDx : D x = D xp + D xo := by rw [hxodef, map_sub]; abel
  have hcross : chartGram (I := I) x₀ p (D v) (D xo) = 0 := by
    rw [hDxo, chartGram_sub_snd', hG x, hDp, chartGram_smul_snd, hG v, hαdef]
    field_simp
    ring
  have hcross2 : chartGram (I := I) x₀ p (D xp) (D xo) = 0 := by
    rw [hDp, chartGram_smul_fst, hcross, mul_zero]
  have hcross3 : chartGram (I := I) x₀ p (D xo) (D xp) = 0 := by
    rw [chartGram_comm, hcross2]
  -- the parallel part has exactly the right norm
  have hpar : chartGram (I := I) x₀ p (D xp) (D xp) = chartGram (I := I) x₀ x₀ xp xp := by
    rw [hDp, chartGram_smul_fst, chartGram_smul_snd, hG v, hxpdef, chartGram_smul_fst,
      chartGram_smul_snd]
  -- the orthogonal part is bounded
  have horth : chartGram (I := I) x₀ p (D xo) (D xo) ≤ chartGram (I := I) x₀ x₀ xo xo := by
    have hb := hflat v xo hvpos hvf ho
    have h1 : chartGram (I := I) x₀ p (D xo) (D xo)
        = ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) xo‖ ^ 2 := by
      rw [chartGram_apply, hframe xo, real_inner_self_eq_norm_sq]
    rw [h1]
    have h2 : 0 ≤ chartGram (I := I) x₀ x₀ xo xo := by
      rw [chartGram_apply]
      exact real_inner_self_nonneg
    have h3 : Real.sqrt (chartGram (I := I) x₀ x₀ xo xo) ^ 2
        = chartGram (I := I) x₀ x₀ xo xo := Real.sq_sqrt h2
    nlinarith [hb, h2, h3, norm_nonneg ((mfderiv 𝓘(ℝ, E) I
      (fun z : E => expMap cov x₀ z) v) xo)]
  -- Pythagoras at `p` and at `x₀`
  have hpyth : chartGram (I := I) x₀ p (D x) (D x)
      = chartGram (I := I) x₀ p (D xp) (D xp) + chartGram (I := I) x₀ p (D xo) (D xo) := by
    rw [hDx, chartGram_add_snd, chartGram_add_fst, chartGram_add_fst, hcross2, hcross3]
    ring
  have hcrossb2 : chartGram (I := I) x₀ x₀ xp xo = 0 := by
    rw [hxpdef, chartGram_smul_fst, ho, mul_zero]
  have hcrossb3 : chartGram (I := I) x₀ x₀ xo xp = 0 := by rw [chartGram_comm, hcrossb2]
  have hbase : chartGram (I := I) x₀ x₀ x x
      = chartGram (I := I) x₀ x₀ xp xp + chartGram (I := I) x₀ x₀ xo xo := by
    conv_lhs => rw [hx]
    rw [chartGram_add_snd, chartGram_add_fst, chartGram_add_fst, hcrossb2, hcrossb3]
    ring
  -- conclusion
  have hfinal : chartGram (I := I) x₀ p (D x) (D x) ≤ chartGram (I := I) x₀ x₀ x x := by
    rw [hpyth, hbase]
    linarith [hpar.le, horth]
  have hnorm : ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖
      = Real.sqrt (chartGram (I := I) x₀ p (D x) (D x)) := by
    rw [← hframe x, chartGram_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm]
  exact Real.sqrt_le_sqrt hfinal


/-! ## 3. The chordal bound -/

/-- **The chordal bound.**  There is `ρ > 0` such that for all `u w : E` of Riemannian norm `< ρ`
at `x₀`, the Riemannian distance between `exp_{x₀} u` and `exp_{x₀} w` is at most the Riemannian
norm of `w - u`:
`d(exp_p u, exp_p w) ≤ ‖w - u‖_p`.

This is the form in which the differential bound is used for the model/hinge comparison. -/
theorem edist_expMap_le_chordal [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u w : E,
      Real.sqrt (chartGram (I := I) x₀ x₀ u u) < ρ →
      Real.sqrt (chartGram (I := I) x₀ x₀ w w) < ρ →
      Manifold.riemannianEDist I (expMap cov x₀ u) (expMap cov x₀ w)
        ≤ ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ (w - u) (w - u))) := by
  obtain ⟨ρn, hρn, hnorm⟩ := mfderiv_expMap_norm_le (cov := cov) hmet htor hpinch x₀
  obtain ⟨ρsm, hρsm, hsm⟩ := Submission.Geodesic.exists_radius_contMDiffAt_expMap (cov := cov) x₀
  obtain ⟨lam, hlam, Lam, hLam, hgram⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I)
    (x₀ := x₀) (K := {x₀}) isCompact_singleton (singleton_nonempty x₀) (by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact mem_chart_source H x₀)
  haveI hcontR : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)
  have hslpos : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hLam
  have hslpos' : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  set δ : ℝ := min ρn ρsm / (Real.sqrt Lam + 1) with hδdef
  have hδpos : 0 < δ := div_pos (lt_min hρn hρsm) (by linarith)
  have hδmin : δ < min ρn ρsm := by
    rw [hδdef, div_lt_iff₀ (by linarith : (0:ℝ) < Real.sqrt Lam + 1)]
    nlinarith [lt_min hρn hρsm, hslpos, mul_pos (lt_min hρn hρsm) hslpos]
  refine ⟨Real.sqrt lam * δ, mul_pos hslpos' hδpos, fun u w hu hw => ?_⟩
  rcases eq_or_ne u w with rfl | hne
  · rw [sub_self, chartGram_zero, Real.sqrt_zero, ENNReal.ofReal_zero,
      Manifold.riemannianEDist_self]
  -- conversions between the metric norm at `x₀` and the ambient norm
  have hamb : ∀ a : E, Real.sqrt (chartGram (I := I) x₀ x₀ a a) < Real.sqrt lam * δ → ‖a‖ < δ := by
    intro a ha
    have hle := (hgram x₀ (by simp) a).1
    have h1 : Real.sqrt lam * ‖a‖ ≤ Real.sqrt (chartGram (I := I) x₀ x₀ a a) := by
      rw [← Real.sqrt_sq (norm_nonneg a), ← Real.sqrt_mul hlam.le]
      exact Real.sqrt_le_sqrt hle
    have h2 : Real.sqrt lam * ‖a‖ < Real.sqrt lam * δ := lt_of_le_of_lt h1 ha
    exact lt_of_mul_lt_mul_left h2 (Real.sqrt_nonneg lam)
  have hmetric : ∀ a : E, ‖a‖ ≤ δ → Real.sqrt (chartGram (I := I) x₀ x₀ a a) < min ρn ρsm := by
    intro a ha
    have hle := (hgram x₀ (by simp) a).2
    have h1 : Real.sqrt (chartGram (I := I) x₀ x₀ a a) ≤ Real.sqrt Lam * ‖a‖ := by
      rw [← Real.sqrt_sq (norm_nonneg a), ← Real.sqrt_mul hLam.le]
      exact Real.sqrt_le_sqrt hle
    have h2 : Real.sqrt Lam * ‖a‖ ≤ Real.sqrt Lam * δ := mul_le_mul_of_nonneg_left ha hslpos.le
    have h3 : Real.sqrt Lam * δ < min ρn ρsm := by
      rw [hδdef]
      have h4 : Real.sqrt Lam * (min ρn ρsm / (Real.sqrt Lam + 1))
          = (Real.sqrt Lam / (Real.sqrt Lam + 1)) * min ρn ρsm := by ring
      rw [h4]
      refine mul_lt_of_lt_one_left (lt_min hρn hρsm) ?_
      rw [div_lt_one (by linarith : (0:ℝ) < Real.sqrt Lam + 1)]
      linarith
    linarith
  have huδ : ‖u‖ < δ := hamb u hu
  have hwδ : ‖w‖ < δ := hamb w hw
  -- the affine path from `u` to `w`
  set σ : ℝ → E := fun t => u + t • (w - u) with hσdef
  set Γ : ℝ → M := fun t => expMap cov x₀ (σ t) with hΓdef
  have hσ0 : σ 0 = u := by simp [hσdef]
  have hσ1 : σ 1 = w := by simp [hσdef]
  have hσaff : ∀ t : ℝ, σ t = (1 - t) • u + t • w := by
    intro t
    rw [hσdef]
    module
  have hσder : ∀ t : ℝ, HasDerivAt σ (w - u) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t • (w - u)) ((1:ℝ) • (w - u)) t :=
      (hasDerivAt_id t).smul_const (w - u)
    rw [one_smul] at h1
    have h2 := h1.const_add u
    have h3 : (fun t : ℝ => u + t • (w - u)) = σ := by
      funext s; rw [hσdef]
    rw [h3] at h2
    exact h2
  have hσnorm : ∀ t ∈ Icc (0:ℝ) 1, ‖σ t‖ ≤ δ := by
    intro t ht
    calc ‖σ t‖ = ‖(1 - t) • u + t • w‖ := by rw [hσaff t]
      _ ≤ ‖(1 - t) • u‖ + ‖t • w‖ := norm_add_le _ _
      _ = (1 - t) * ‖u‖ + t * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * δ + t * δ := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left huδ.le (by linarith [ht.2])
          · exact mul_le_mul_of_nonneg_left hwδ.le ht.1
      _ = δ := by ring
  -- smoothness of the path
  have hσsm : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ σ := by
    rw [contMDiff_iff_contDiff, hσdef]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hΓsm : CMDiff[Icc (0:ℝ) 1] 1 Γ := by
    have h1 : ContMDiffOn 𝓘(ℝ) I ∞ Γ (Icc (0:ℝ) 1) := by
      intro t ht
      have hσb : ‖σ t‖ < ρsm := lt_of_lt_of_le (lt_of_le_of_lt (hσnorm t ht) hδmin)
        (min_le_right _ _)
      have h2 : ContMDiffAt 𝓘(ℝ) I ∞ (fun z : ℝ => expMap cov x₀ (σ z)) t :=
        (hsm (σ t) hσb).comp t hσsm.contMDiffAt
      exact h2.contMDiffWithinAt
    exact h1.of_le (WithTop.coe_le_coe.mpr le_top)
  -- distance ≤ length
  have hdist : Manifold.riemannianEDist I (Γ 0) (Γ 1) ≤ Manifold.pathELength I Γ 0 1 :=
    Submission.EDist.riemannianEDist_le_pathELength (I := I) hΓsm
      (by simp only [hΓdef, hσ0]) (by simp only [hΓdef, hσ1]) zero_le_one
  -- the length as an integral
  have hlen : Manifold.pathELength I Γ 0 1
      = ∫⁻ t in Icc (0:ℝ) 1, ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ :=
    Manifold.pathELength_eq_lintegral_mfderiv_Icc
  -- the integrand bound, almost everywhere
  set c : ℝ := Real.sqrt (chartGram (I := I) x₀ x₀ (w - u) (w - u)) with hcdef
  have hcnonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hzero : ({t : ℝ | σ t = 0}).Subsingleton := by
    intro t ht0 t' ht0'
    have h1 : u + t • (w - u) = u + t' • (w - u) := by
      have := ht0.trans ht0'.symm
      simpa only [hσdef] using this
    have h2 : (t - t') • (w - u) = 0 := by
      have h2a : u + t • (w - u) - (u + t' • (w - u)) = 0 := by rw [h1]; abel
      have h2b : u + t • (w - u) - (u + t' • (w - u)) = (t - t') • (w - u) := by module
      rw [← h2b]; exact h2a
    have h3 : t = t' ∨ w - u = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · left; linarith
      · right; exact h
    rcases h3 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hne)
  have hae0 : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Icc (0:ℝ) 1)), σ t ≠ 0 := by
    have hnull : MeasureTheory.volume {t : ℝ | σ t = 0} = 0 := by
      rcases hzero.eq_empty_or_singleton with hemp | ⟨a, ha⟩
      · rw [hemp]; simp
      · rw [ha]; exact Real.volume_singleton
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine (MeasureTheory.ae_iff).mpr ?_
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro a ha
    by_contra h
    exact ha (fun _ => h)
  have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Icc (0:ℝ) 1)),
      ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c := by
    filter_upwards [hae0, MeasureTheory.ae_restrict_mem measurableSet_Icc] with t hne ht
    have hcv : curveVelocity (I := I) Γ t
        = (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) (σ t)) (w - u) := by
      have h := Submission.Minimal.curveVelocity_eq_exp_deriv (cov := cov) (x₀ := x₀)
        (σ := σ) (σ' := fun _ => w - u) (γ := Γ) (t := t) (hσder t)
        ((hsm (σ t) (lt_of_lt_of_le (lt_of_le_of_lt (hσnorm t ht) hδmin) (min_le_right _ _)))
          |>.mdifferentiableAt (by simp))
        (Filter.EventuallyEq.of_eq (by funext s; rw [hΓdef]))
      exact h
    have hpos : 0 < chartGram (I := I) x₀ x₀ (σ t) (σ t) := by
      rcases lt_or_eq_of_le (Submission.Minimal.chartGram_self_nonneg (I := I) x₀ x₀ (σ t))
        with h | h
      · exact h
      · exfalso
        exact hne ((chartGram_self_eq_zero_iff (I := I) (mem_chart_source H x₀) (σ t)).mp h.symm)
    have hb := hnorm (σ t) (w - u) hpos
      (lt_of_lt_of_le (hmetric (σ t) (hσnorm t ht)) (min_le_left ρn ρsm))
    have he₁ : ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ
        = ENNReal.ofReal ‖curveVelocity (I := I) Γ t‖ := by
      change ‖curveVelocity (I := I) Γ t‖ₑ = _
      rw [Submission.Minimal.enorm_eq_ofReal_norm]
    rw [he₁, hcv, hcdef]
    exact ENNReal.ofReal_le_ofReal hb
  -- integrate
  have hconst : ∫⁻ _ in Icc (0:ℝ) 1, ENNReal.ofReal c = ENNReal.ofReal c := by
    rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
    norm_num
  calc Manifold.riemannianEDist I (expMap cov x₀ u) (expMap cov x₀ w)
      = Manifold.riemannianEDist I (Γ 0) (Γ 1) := by
        congr 1
        · show expMap cov x₀ u = expMap cov x₀ (σ 0)
          rw [hσ0]
        · show expMap cov x₀ w = expMap cov x₀ (σ 1)
          rw [hσ1]
    _ ≤ Manifold.pathELength I Γ 0 1 := hdist
    _ = ∫⁻ t in Icc (0:ℝ) 1, ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ := hlen
    _ ≤ ∫⁻ _ in Icc (0:ℝ) 1, ENNReal.ofReal c := MeasureTheory.lintegral_mono_ae hae
    _ = ENNReal.ofReal c := hconst


/-- The radial case of the chordal bound: for `w` of small Riemannian norm at `x₀`,
`d(x₀, exp_{x₀} w) ≤ ‖w‖`. -/
theorem edist_zero_expMap_le [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : E,
      Real.sqrt (chartGram (I := I) x₀ x₀ w w) < ρ →
      Manifold.riemannianEDist I x₀ (expMap cov x₀ w)
        ≤ ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ w w)) := by
  obtain ⟨ρ, hρ, hb⟩ := edist_expMap_le_chordal (cov := cov) hmet htor hpinch x₀
  refine ⟨ρ, hρ, fun w hw => ?_⟩
  have h0 : Real.sqrt (chartGram (I := I) x₀ x₀ (0 : E) (0 : E)) = 0 := by
    rw [chartGram_zero, Real.sqrt_zero]
  have h := hb 0 w (by rw [h0]; exact hρ) hw
  rw [Submission.Geodesic.expMap_zero (cov := cov) x₀] at h
  simpa using h

end

end Submission.ExpBound2
