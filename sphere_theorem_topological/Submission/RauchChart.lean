import Submission.RauchGen
import Submission.ExpBound2
import Submission.ChartGeoAt

/-!
# Rauch's upper comparison for a chart geodesic with an arbitrary base point

`Submission.ExpBound2.rauch_bound_rescaled` proves Rauch's upper bound for a chart geodesic whose
base point is the *centre* of the chart.  For the uniform local comparison theorem one needs the
same bound for a chart geodesic that starts at an arbitrary point `q` of a fixed chart, described in
the coordinates of that chart.  This file restates the theorem in that generality
(`rauch_bound_arbitrary_base`); the proof is the same as in `ExpBound2`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.Curvature
open Submission.Rauch
open Submission.JacobiTensor
open Submission.RauchGen
open Submission.JacobiGen

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.RauchChart

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Rauch's bound for a rescaled (unit-speed) chart geodesic with an arbitrary base point.**  Let
`(u,w)` be a chart geodesic in the chart at `x₀`, starting at an arbitrary point `q` of the chart,
whose metric speed is `c > 0` (so that `s ↦ (u (s/c), c⁻¹ w (s/c))` has unit metric speed), and let
`(Y,U)` be the Jacobi tensor along it with `Y 0 = 0`, `U 0 = 1`.  Then for `x ⊥ v` (in the chart
metric at the base point `q`) with `c < π/3`,

`⟨(Y 1) x, (Y 1) x⟩ ≤ sin(c)² c⁻² ⟨x,x⟩`.

Here `v : E` is the *coordinate* velocity of the geodesic at the base point (i.e. `w 0`). -/
theorem rauch_bound_arbitrary_base {x₀ q : M} {v x : E} {u w : ℝ → E} {Y U : ℝ → E →L[ℝ] E}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hqs : q ∈ (extChartAt I x₀).source)
    (hgc : HasChartGeodesicOn cov x₀ q (frameVector (I := I) x₀ q v) u w (-2) 2)
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)
        = chartGram (I := I) x₀ q v v)
    {c : ℝ} (hc : 0 < c) (hcsq : c ^ 2 = chartGram (I := I) x₀ q v v)
    (hc3 : c < Real.pi / 3)
    (hY : ∀ t ∈ Icc (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1)
    (horth : chartGram (I := I) x₀ q v x = 0) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 1)) ((Y 1) x) ((Y 1) x)
      ≤ Real.sin c ^ 2 * ((c⁻¹) ^ 2 * chartGram (I := I) x₀ q x x) := by
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
  have hgeo : HasChartGeodesicOn cov x₀ q (c⁻¹ • frameVector (I := I) x₀ q v) ut wt
      (-(3 * c / 2)) (3 * c / 2) := by
    refine ⟨?_, ?_, ?_, hgeod, hgeod2⟩
    · change u (c⁻¹ * 0) = (extChartAt I x₀) q
      rw [mul_zero]; exact hgc.1
    · change c⁻¹ • w (c⁻¹ * 0)
        = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q
            (c⁻¹ • frameVector (I := I) x₀ q v)
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
    exact Submission.ExpBound2.gammaOp_scale (cov := cov) x₀ (u := u) (w := w) (t := c⁻¹ * s) c⁻¹
  have hR : ∀ s ∈ Ioo (-(3 * c / 2)) (3 * c / 2),
      curvOp (cov := cov) x₀ ut wt s = (c⁻¹) ^ 2 • curvOp (cov := cov) x₀ u w (c⁻¹ * s) := by
    intro s hs
    change curvOp (cov := cov) x₀ (fun s' => u (c⁻¹ * s'))
      (fun s' => c⁻¹ • w (c⁻¹ * s')) s = (c⁻¹) ^ 2 • curvOp (cov := cov) x₀ u w (c⁻¹ * s)
    exact Submission.ExpBound2.curvOp_smul_mid (cov := cov) htor x₀ (u := u) (w := w) (t := c⁻¹ * s)
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
  let D : JData cov x₀ q (c⁻¹ • frameVector (I := I) x₀ q v) ut wt
      (-(3 * c / 2)) (3 * c / 2) :=
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
  have hut0 : ut 0 = (extChartAt I x₀) q := by
    change u (c⁻¹ * 0) = (extChartAt I x₀) q
    rw [mul_zero]; exact hgc.1
  have hbase0 : (extChartAt I x₀).symm (ut 0) = q := by
    rw [hut0]
    exact (extChartAt I x₀).left_inv hqs
  have hw0v : w 0 = v := by
    rw [hgc.2.1]
    exact Trivialization.continuousLinearMapAt_symmL (trivializationAt E (TangentSpace I) x₀)
      (R := ℝ) (by simpa using hqs) v
  have horth_res : chartGram (I := I) x₀ ((extChartAt I x₀).symm (ut 0)) (c⁻¹ • x) (wt 0) = 0 := by
    change chartGram (I := I) x₀ ((extChartAt I x₀).symm (u (c⁻¹ * 0))) (c⁻¹ • x)
      (c⁻¹ • w (c⁻¹ * 0)) = 0
    rw [mul_zero, hgc.1, (extChartAt I x₀).left_inv hqs, hw0v]
    change chartGram (I := I) x₀ q (c⁻¹ • x) (c⁻¹ • v) = 0
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
      = (c⁻¹) ^ 2 * chartGram (I := I) x₀ q x x := by
    rw [hbase0, chartGram_smul_fst, chartGram_smul_snd]
    ring
  rw [hutc, hYc, hbase] at hmain
  exact hmain


end

end Submission.RauchChart
