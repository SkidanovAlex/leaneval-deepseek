import Submission.GExpRay2
import Submission.CutPoint

/-!
# Continuity of `GExp p` *at* the points of the injectivity ball

`Submission.GExpRay2.continuousOn_GExp_closedBall_of_injAtLeast` proves that the exponential map
`F = GExp p` is continuous *within* the closed ball of radius `inj(p)`.  What the cut-point
argument needs is continuity **at** those points, i.e. for sequences `V n → v` with `‖v‖ ≤ m` whose
terms may lie *outside* the ball.  This file proves exactly that:

* `tendsto_GExp_of_tendsto_of_norm_le` — if `InjAtLeast hmet p m`, `V n → v` and `‖v‖ ≤ m`, then
  `GExp p (V n) → GExp p v`.

The proof uses the **ray bound** in a crucial way.  For `‖v‖ = m` (the only case where the ball
continuity does not apply directly) set `nS w := (m / ‖w‖) • w`, the renormalisation of `w` to the
sphere of radius `m` (and `nS 0 = 0`).  Then

* `nS w → v` whenever `w → v` with `‖v‖ = m`, and `‖nS w‖ = m`, so `F (nS w) → F v` by continuity
  *within* the closed ball;
* `w` and `nS w` lie on the **same ray**, so `d(F w, F (nS w)) ≤ |‖w‖ - m|` by the ray bound, and
  that tends to `0`.

This is the observation that makes the "fold" harmless at the *boundary* of the injectivity ball:
continuity of `F` at a point of norm exactly `m` follows from continuity *inside* the ball together
with the elementary ray estimate — no global geodesic flow is needed.  (See
`Submission/Roadmap.lean` §74 for what *is* still missing: the *local injectivity* of `F`, i.e. the
non-conjugate-point statement.)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.ChartBounds
open Submission.GExpRay
open Submission.InjRadius
open Submission.GExpRay2
open Submission.CutWitness

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpBoundary

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {p : M}

/-- **The renormalisation of a tangent vector to the sphere of radius `m`**: `nS w = (m/‖w‖) • w`
(and `nS 0 = 0` since division by zero is `0`).  For `w ≠ 0` it lies on the ray of `w` and has
norm `m`. -/
noncomputable def normSpherical (m : ℝ) (w : TangentSpace I p) : TangentSpace I p :=
  (m / ‖w‖) • w

lemma normSpherical_apply {m : ℝ} (w : TangentSpace I p) :
    normSpherical (I := I) m w = (m / ‖w‖) • w := rfl

lemma norm_normSpherical {m : ℝ} (hm : 0 ≤ m) {w : TangentSpace I p} (hw : w ≠ 0) :
    ‖normSpherical (I := I) m w‖ = m := by
  rw [normSpherical_apply, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (norm_nonneg w), abs_of_nonneg hm]
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  field_simp

lemma norm_normSpherical_le {m : ℝ} (hm : 0 ≤ m) (w : TangentSpace I p) :
    ‖normSpherical (I := I) m w‖ ≤ m := by
  by_cases hw : w = 0
  · rw [hw, normSpherical_apply, norm_zero, div_zero, zero_smul, norm_zero]; exact hm
  · rw [norm_normSpherical hm hw]

lemma normSpherical_self {m : ℝ} {v : TangentSpace I p} (hv : ‖v‖ = m) :
    normSpherical (I := I) m v = v := by
  rw [normSpherical_apply, hv]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [zero_div, zero_smul]
    exact (norm_eq_zero.mp hv).symm
  · rw [div_self hm, one_smul]

/-- **The ray bound for the renormalisation**: `F w` and `F (nS w)` are on the same ray, at
parameters `‖w‖` and `m`. -/
lemma edist_normSpherical_le (hmet : IsMetricCompatible cov) {m : ℝ} (hm : 0 ≤ m)
    (w : TangentSpace I p) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet p w)
        (GExp (cov := cov) hmet p (normSpherical (I := I) m w))
      ≤ ENNReal.ofReal |‖w‖ - m| := by
  by_cases hw : w = 0
  · subst hw
    have h0 : normSpherical (I := I) m (0 : TangentSpace I p) = 0 := by
      rw [normSpherical_apply, norm_zero, div_zero, zero_smul]
    rw [h0, GExp_zero, Manifold.riemannianEDist_self, norm_zero, zero_sub]
    exact bot_le
  · set ξ : TangentSpace I p := unitOf w hw with hξdef
    have hξ : ‖ξ‖ = 1 := unitOf_norm w hw
    have hwξ : ‖w‖ • ξ = w := by
      rw [hξdef]
      show ‖w‖ • unitOf w hw = w
      rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
    have hnS : normSpherical (I := I) m w = m • ξ := by
      have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      have hwξ' : ‖w‖ • ξ = w := hwξ
      calc normSpherical (I := I) m w
          = (m / ‖w‖) • w := normSpherical_apply w
        _ = (m / ‖w‖) • (‖w‖ • ξ) := congrArg (fun z => (m / ‖w‖) • z) hwξ'.symm
        _ = ((m / ‖w‖) * ‖w‖) • ξ := smul_smul _ _ _
        _ = m • ξ := by rw [div_mul_cancel₀ m hwn]
    rcases le_total ‖w‖ m with hle | hle
    · have h := edist_GExp_smul_le_mul_norm (cov := cov) hmet p (v := ξ)
        (a := ‖w‖) (b := m) (norm_nonneg w) hle
      rw [hwξ, hξ, mul_one] at h
      rw [hnS, abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
      exact h
    · have h := edist_GExp_smul_le_mul_norm (cov := cov) hmet p (v := ξ)
        (a := m) (b := ‖w‖) hm hle
      rw [hwξ, hξ, mul_one, Manifold.riemannianEDist_comm] at h
      rw [hnS, abs_of_nonneg (sub_nonneg.mpr hle)]
      exact h

/-- **The renormalisation is continuous** at a *non-zero* limit. -/
lemma tendsto_normSpherical {m : ℝ} {v : TangentSpace I p} {V : ℕ → TangentSpace I p}
    (hv : v ≠ 0) (hV : Tendsto V atTop (𝓝 v)) :
    Tendsto (fun n => normSpherical (I := I) m (V n)) atTop (𝓝 (normSpherical (I := I) m v)) := by
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have h1 : Tendsto (fun n => ‖V n‖) atTop (𝓝 ‖v‖) := hV.norm
  have h2 : Tendsto (fun n => (m / ‖V n‖) • V n) atTop (𝓝 ((m / ‖v‖) • v)) :=
    (tendsto_const_nhds.div h1 hvnorm).smul hV
  simpa only [normSpherical_apply] using h2

/-- **Continuity of `GExp p` at the points of the injectivity ball**, sequence form. -/
theorem tendsto_GExp_of_tendsto_of_norm_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] {m : ℝ} (hinj : InjAtLeast hmet p m)
    {v : TangentSpace I p} {V : ℕ → TangentSpace I p}
    (hV : Tendsto V atTop (𝓝 v)) (hv : ‖v‖ ≤ m) :
    Tendsto (fun n => GExp (cov := cov) hmet p (V n)) atTop
      (𝓝 (GExp (cov := cov) hmet p v)) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hcont : ContinuousOn (fun w : TangentSpace I p => GExp (cov := cov) hmet p w)
      (Metric.closedBall (0 : TangentSpace I p) m) :=
    Submission.GExpRay2.continuousOn_GExp_closedBall_of_injAtLeast (cov := cov) hmet htor hinj m le_rfl
  by_cases hv0 : v = 0
  · subst hv0
    rw [GExp_zero]
    refine EMetric.tendsto_nhds.mpr (fun ε hε => ?_)
    have hmem2 : Set.Iio ε ∈ 𝓝 (0 : ℝ≥0∞) := Iio_mem_nhds hε
    have hlim : Tendsto (fun n => ENNReal.ofReal ‖V n‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => ‖V n‖) atTop (𝓝 0) := by simpa using hV.norm
      have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp h0
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using h1
    filter_upwards [hlim.eventually hmem2] with n hn
    refine lt_of_le_of_lt ?_ hn
    rw [Submission.EDist.edist_eq_riemannianEDist (I := I), Manifold.riemannianEDist_comm]
    exact edist_GExp_le_norm (cov := cov) hmet (V n)
  · by_cases hlt : ‖v‖ < m
    · have hmem : v ∈ Metric.ball (0 : TangentSpace I p) m := by
        rw [Metric.mem_ball, dist_zero_right]; exact hlt
      have hnb : Metric.closedBall (0 : TangentSpace I p) m ∈ 𝓝 v :=
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem) Metric.ball_subset_closedBall
      have hcw : ContinuousWithinAt (fun w : TangentSpace I p => GExp (cov := cov) hmet p w)
          (Metric.closedBall (0 : TangentSpace I p) m) v :=
        hcont v (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hlt)
      exact (hcw.continuousAt hnb).tendsto.comp hV
    · have hvm : ‖v‖ = m := le_antisymm hv (not_lt.mp hlt)
      have hmn : (0 : ℝ) ≤ m := hvm ▸ norm_nonneg v
      have hWtend : Tendsto (fun n => normSpherical (I := I) m (V n)) atTop (𝓝 v) := by
        have h := tendsto_normSpherical (I := I) (m := m) hv0 hV
        rwa [normSpherical_self (I := I) hvm] at h
      have hWmem : ∀ n,
          normSpherical (I := I) m (V n) ∈ Metric.closedBall (0 : TangentSpace I p) m := by
        intro n
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_normSpherical_le (I := I) hmn (V n)
      have hWlim : Tendsto (fun n => GExp (cov := cov) hmet p (normSpherical (I := I) m (V n)))
          atTop (𝓝 (GExp (cov := cov) hmet p v)) :=
        (hcont v (by rw [Metric.mem_closedBall, dist_zero_right]; exact hv)).tendsto.comp
          (tendsto_nhdsWithin_iff.mpr ⟨hWtend, Eventually.of_forall hWmem⟩)
      have hray : ∀ n, edist (GExp (cov := cov) hmet p (V n))
          (GExp (cov := cov) hmet p (normSpherical (I := I) m (V n)))
          ≤ ENNReal.ofReal |‖V n‖ - m| := by
        intro n
        rw [Submission.EDist.edist_eq_riemannianEDist (I := I)]
        exact edist_normSpherical_le (cov := cov) hmet (m := m) hmn (V n)
      have hlim : Tendsto (fun n => ENNReal.ofReal |‖V n‖ - m|) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n => |‖V n‖ - m|) atTop (𝓝 0) := by
          have h0' : Tendsto (fun n => ‖V n‖ - m) atTop (𝓝 (‖v‖ - m)) :=
            hV.norm.sub (tendsto_const_nhds (x := m))
          have h : Tendsto (fun n => |‖V n‖ - m|) atTop (𝓝 |‖v‖ - m|) := h0'.abs
          rw [hvm, sub_self, abs_zero] at h
          simpa using h
        have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp h0
        simpa only [Function.comp_def, ENNReal.ofReal_zero] using h1
      have hb : Tendsto (fun n => edist (GExp (cov := cov) hmet p (V n))
          (GExp (cov := cov) hmet p (normSpherical (I := I) m (V n)))) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
          (fun _ => bot_le) hray
      refine EMetric.tendsto_nhds.mpr (fun ε hε => ?_)
      have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
      have hmem2 : Set.Iio (ε / 2) ∈ 𝓝 (0 : ℝ≥0∞) := Iio_mem_nhds hε2
      have h2 : ∀ᶠ n in atTop,
          edist (GExp (cov := cov) hmet p (normSpherical (I := I) m (V n)))
            (GExp (cov := cov) hmet p v) < ε / 2 :=
        (EMetric.tendsto_nhds.mp hWlim) (ε / 2) hε2
      have h3 : ∀ᶠ n in atTop, edist (GExp (cov := cov) hmet p (V n))
          (GExp (cov := cov) hmet p (normSpherical (I := I) m (V n))) < ε / 2 :=
        hb.eventually hmem2
      filter_upwards [h3, h2] with n hn3 hn2
      calc edist (GExp (cov := cov) hmet p (V n)) (GExp (cov := cov) hmet p v)
          ≤ edist (GExp (cov := cov) hmet p (V n))
              (GExp (cov := cov) hmet p (normSpherical (I := I) m (V n)))
            + edist (GExp (cov := cov) hmet p (normSpherical (I := I) m (V n)))
              (GExp (cov := cov) hmet p v) := edist_triangle _ _ _
        _ < ε := by
            rw [← ENNReal.add_halves ε]
            exact ENNReal.add_lt_add hn3 hn2

end

end Submission.GExpBoundary
