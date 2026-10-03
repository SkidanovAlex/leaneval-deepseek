import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

open Complex MeasureTheory Metric Set Topology
open scoped Real Topology BigOperators Interval

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Commons.Analysis.Complex

/-! # Bound for the log-derivative contour integral on a circle

The statement `circleLogDerivContour_bound` bounds
`‖(1 / (2πi)) ∮_{|w|=ρ} (f'/f)(w) (1/(s-w) - 1/((0)-w)) dw‖`
for a holomorphic function `f` with no zeros on the circle, given a pointwise
log-derivative bound `hLDE`, a zero count `hzc` in the disk of radius `ρ+1`
and the "good radius" gap hypothesis `hgap` (zeros stay at distance at least
`1/(log(R+2)+A)²` from the circle).

Strategy: parametrise the circle by `circleMap 0 ρ θ`; on the circle write
`1/(s-w) - 1/((0)-w) = s/(w(s-w))` and estimate the contour integral by the
L1-norm of `f'/f` over the circle.  The `hLDE` divisor sum is matched against
the global divisor (zeros with `‖u‖ ≤ ρ+1`), each zero `u` contributes
`∫ circleTheta u ρ θ dθ ≤ (16/ρ)/|‖u‖−ρ| ≤ (16/ρ)·(log(R+2)+A)²` (commons
`circleBallTheta_integral_inv_le`), and the total multiplicity is bounded by
`hzc`.
-/

/-! ## Circle integral norm bound -/

lemma circleIntegral_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) {f : ℂ → ℂ} :
    ‖∮ z in C(0, ρ), f z‖ ≤ ρ * ∫ θ in 0..(2 * Real.pi), ‖f (_root_.circleMap 0 ρ θ)‖ := by
  unfold circleIntegral
  calc
    ‖∫ θ in 0..2 * Real.pi, deriv (_root_.circleMap 0 ρ) θ • f (_root_.circleMap 0 ρ θ)‖
        ≤ ∫ θ in 0..2 * Real.pi, ‖deriv (_root_.circleMap 0 ρ) θ • f (_root_.circleMap 0 ρ θ)‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm
            (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    _ = ∫ θ in 0..2 * Real.pi, ‖(_root_.circleMap 0 ρ θ * I) • f (_root_.circleMap 0 ρ θ)‖ := by
          refine intervalIntegral.integral_congr ?_
          intro θ hθ
          change ‖deriv (_root_.circleMap 0 ρ) θ • f (_root_.circleMap 0 ρ θ)‖ =
            ‖(_root_.circleMap 0 ρ θ * I) • f (_root_.circleMap 0 ρ θ)‖
          rw [deriv_circleMap]
    _ = ∫ θ in 0..2 * Real.pi, ‖_root_.circleMap 0 ρ θ * I‖ * ‖f (_root_.circleMap 0 ρ θ)‖ := by
          refine intervalIntegral.integral_congr ?_
          intro θ hθ
          change ‖(_root_.circleMap 0 ρ θ * I) • f (_root_.circleMap 0 ρ θ)‖ =
            ‖_root_.circleMap 0 ρ θ * I‖ * ‖f (_root_.circleMap 0 ρ θ)‖
          rw [norm_smul]
    _ = ∫ θ in 0..2 * Real.pi, ρ * ‖f (_root_.circleMap 0 ρ θ)‖ := by
          refine intervalIntegral.integral_congr ?_
          intro θ hθ
          change ‖_root_.circleMap 0 ρ θ * I‖ * ‖f (_root_.circleMap 0 ρ θ)‖ =
            ρ * ‖f (_root_.circleMap 0 ρ θ)‖
          congr 1
          simp [norm_mul, norm_I, norm_circleMap_zero, abs_of_nonneg hρ]
    _ = ρ * ∫ θ in 0..2 * Real.pi, ‖f (_root_.circleMap 0 ρ θ)‖ := by
          rw [intervalIntegral.integral_const_mul]

lemma norm_scaled_circle_le (X : ℂ) :
    ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) • X)‖ ≤ (1 / (2 * Real.pi)) * ‖X‖ := by
  rw [norm_smul]
  have hden : ‖(2 * (Real.pi : ℂ) * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I) = (2 : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < Real.pi), norm_I]
  have hc : ‖(1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)‖ ≤ (1 / (2 * Real.pi)) := by
    rw [norm_div]
    rw [hden]
    rw [norm_one]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg X)

/-! ## The kernel `1/(s-w) - 1/((0)-w) = s/(w(s-w))` -/

lemma kernel_eq {ρ : ℝ} {s w : ℂ} (hρ : 0 < ρ) (hsw : ‖s‖ < ρ) (hw : ‖w‖ = ρ) :
    (1 / (s - w) - 1 / ((0 : ℂ) - w)) = s / (w * (s - w)) := by
  have hw0 : w ≠ 0 := by
    intro h
    have : ‖w‖ = 0 := by simp [h]
    have : ρ = 0 := by linarith [hw]
    linarith
  have hws : s - w ≠ 0 := by
    intro h
    have hs_eq : s = w := sub_eq_zero.mp h
    have h2 : ‖s‖ = ρ := by simpa [hs_eq] using hw
    linarith [hsw, h2]
  have hw0' : (0 : ℂ) - w ≠ 0 := by simp [hw0]
  field_simp [hw0, hws, hw0']
  ring

lemma kernel_norm_le {ρ : ℝ} {s w : ℂ} (hρ : 0 < ρ) (hsw : ‖s‖ < ρ) (hw : ‖w‖ = ρ) :
    ‖s / (w * (s - w))‖ ≤ ‖s‖ / (ρ * (ρ - ‖s‖)) := by
  have hw0 : w ≠ 0 := by
    intro h
    have : ‖w‖ = 0 := by simp [h]
    have : ρ = 0 := by linarith [hw]
    linarith
  have hws_ne : s - w ≠ 0 := by
    intro h
    have hs_eq : s = w := sub_eq_zero.mp h
    have h2 : ‖s‖ = ρ := by simpa [hs_eq] using hw
    linarith [hsw, h2]
  have hρs_pos : 0 < ρ - ‖s‖ := by linarith
  have htri : ρ - ‖s‖ ≤ ‖s - w‖ := by
    have hw2 : ‖w‖ ≤ ‖w - s‖ + ‖s‖ := by
      calc ‖w‖ = ‖(w - s) + s‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - s‖ + ‖s‖ := norm_add_le _ _
    have hw2' : ρ ≤ ‖s - w‖ + ‖s‖ := by
      simpa [hw, norm_sub_rev] using hw2
    linarith
  have hden : 0 < ρ * (ρ - ‖s‖) := mul_pos hρ hρs_pos
  have hρ_le : ρ * (ρ - ‖s‖) ≤ ρ * ‖s - w‖ :=
    mul_le_mul_of_nonneg_left htri hρ.le
  calc
    ‖s / (w * (s - w))‖ = ‖s‖ / ‖w * (s - w)‖ := by rw [norm_div]
    _ = ‖s‖ / (‖w‖ * ‖s - w‖) := by rw [norm_mul]
    _ = ‖s‖ / (ρ * ‖s - w‖) := by rw [hw]
    _ ≤ ‖s‖ / (ρ * (ρ - ‖s‖)) := by
      exact div_le_div_of_nonneg_left (norm_nonneg s) hden hρ_le

lemma kernel_abs_le {ρ : ℝ} {s w : ℂ} (hρ : 0 < ρ) (hsw : ‖s‖ < ρ) (hw : ‖w‖ = ρ) :
    ‖(1 / (s - w) - 1 / ((0 : ℂ) - w))‖ ≤ ‖s‖ / (ρ * (ρ - ‖s‖)) := by
  rw [kernel_eq hρ hsw hw]
  exact kernel_norm_le hρ hsw hw

/-! ## Divisor facts for an entire function -/

lemma divisor_nonneg_on_closedBall {f : ℂ → ℂ} {a : ℂ} {ρ : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall a ρ)) (u : ℂ) :
    (0 : ℝ) ≤ (((MeromorphicOn.divisor f (closedBall a ρ)) u : ℤ) : ℝ) := by
  have hz : 0 ≤ (MeromorphicOn.divisor f (closedBall a ρ)) u := by
    by_cases hu : u ∈ closedBall a ρ
    · exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf) u
    · rw [MeromorphicOn.divisor_def, if_neg]
      intro h; exact hu h.2
  exact_mod_cast hz

lemma divisor_eq_zero_of_not_mem {f : ℂ → ℂ} (U : Set ℂ) {u : ℂ} (hu : u ∉ U) :
    (MeromorphicOn.divisor f U) u = 0 := by
  rw [MeromorphicOn.divisor_def, if_neg]
  intro h; exact hu h.2

lemma divisor_mem_of_ne_zero {f : ℂ → ℂ} {a : ℂ} {ρ : ℝ} {u : ℂ}
    (h : (MeromorphicOn.divisor f (closedBall a ρ)) u ≠ 0) : u ∈ closedBall a ρ := by
  by_contra hu
  exact h (divisor_eq_zero_of_not_mem (closedBall a ρ) hu)

lemma divisor_support_finite_closedBall {f : ℂ → ℂ} {a : ℂ} {ρ : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall a ρ)) :
    (Function.support (MeromorphicOn.divisor f (closedBall a ρ))).Finite := by
  exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall a ρ)
    (U := Metric.closedBall a ρ) hf.meromorphicOn (isCompact_closedBall a ρ)
    (by intro z hz; exact hz)

lemma zero_of_divisor_ne_zero {f : ℂ → ℂ} {a : ℂ} {ρ : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall a ρ)) {u : ℂ}
    (hdu : (MeromorphicOn.divisor f (closedBall a ρ)) u ≠ 0) : f u = 0 := by
  have hu : u ∈ closedBall a ρ := divisor_mem_of_ne_zero hdu
  by_contra hfu
  have hord0 : (analyticOrderAt f u).map (↑) = (0 : WithTop ℤ) := by
    have ho : analyticOrderAt f u = 0 := (hf u hu).analyticOrderAt_eq_zero.mpr hfu
    rw [ho]
    simp
  have hdv : (MeromorphicOn.divisor f (closedBall a ρ)) u = 0 := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hu]
    simp [hord0]
  exact hdu hdv

lemma analyticOnNhd_closedBall_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (B : Set ℂ) : AnalyticOnNhd ℂ f B := by
  intro z hz
  exact hf.analyticAt z

/-! Local divisor sum equals the sum over the global (radius `ρ + 1`) zero set. -/
lemma localDivisor_eq_global (f : ℂ → ℂ) {ρ : ℝ} {w : ℂ} (hwρ : ‖w‖ = ρ)
    (hfAn : AnalyticOnNhd ℂ f (Metric.closedBall w 1 ∪ Metric.closedBall (0 : ℂ) (ρ + 1))) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall w 1)) u : ℤ) : ℝ) * (‖w - u‖ : ℝ)⁻¹) =
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) (ρ + 1))) u : ℤ) : ℝ) *
        (if ‖u - w‖ ≤ 1 then (‖u - w‖ : ℝ)⁻¹ else 0)) := by
  classical
  let dloc : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall w 1) u
  let dg : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) (ρ + 1)) u
  have hfAn_loc : AnalyticOnNhd ℂ f (Metric.closedBall w 1) := by
    intro z hz; exact hfAn z (by simp [hz])
  have hfAn_g : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) (ρ + 1)) := by
    intro z hz; exact hfAn z (by simp [hz])
  have hlocFin : (Function.support dloc).Finite := by
    dsimp [dloc]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall w 1)
      (U := Metric.closedBall w 1) hfAn_loc.meromorphicOn (isCompact_closedBall w 1)
      (by intro z hz; exact hz)
  have hgFin : (Function.support dg).Finite := by
    dsimp [dg]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall (0 : ℂ) (ρ + 1))
      (U := Metric.closedBall (0 : ℂ) (ρ + 1)) hfAn_g.meromorphicOn
      (isCompact_closedBall (0 : ℂ) (ρ + 1)) (by intro z hz; exact hz)
  let S : Finset ℂ := hgFin.toFinset
  have hmemS : ∀ {u : ℂ}, dg u ≠ 0 → u ∈ S := by
    intro u h; exact (hgFin.mem_toFinset).mpr h
  -- coefficient-wise agreement
  have hcoeff : ∀ u, (((dloc u : ℤ) : ℝ) * (‖w - u‖ : ℝ)⁻¹) =
      (((dg u : ℤ) : ℝ) * (if ‖u - w‖ ≤ 1 then (‖u - w‖ : ℝ)⁻¹ else 0)) := by
    intro u
    by_cases hu : ‖u - w‖ ≤ 1
    · have huB1 : u ∈ Metric.closedBall w 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
      have huB2 : u ∈ Metric.closedBall (0 : ℂ) (ρ + 1) := by
        have htri2 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := by
          have h2 : ‖u‖ = ‖(u - w) + w‖ := congrArg norm (by ring : u = (u - w) + w)
          rw [h2]
          simpa [add_comm] using norm_add_le (u - w) w
        have hgoal : ‖u‖ ≤ ρ + 1 := by nlinarith [htri2, hwρ, hu]
        simpa [Metric.mem_closedBall, dist_eq_norm] using hgoal
      have heq : dloc u = dg u := by
        dsimp [dloc, dg]
        exact Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (f := f) (a := w) (b := (0 : ℂ))
          (ra := 1) (rb := ρ + 1) (u := u) hfAn huB1 huB2
      have hnorm : ‖w - u‖ = ‖u - w‖ := norm_sub_rev w u
      rw [heq, hnorm]
      simp [hu]
    · have huB1 : u ∉ Metric.closedBall w 1 := by
        intro h
        have : ‖u - w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using h
        exact hu this
      have hdloc0 : dloc u = 0 := by
        dsimp [dloc]
        rw [MeromorphicOn.divisor_def]
        rw [if_neg]
        intro h; exact huB1 h.2
      rw [hdloc0]
      simp [hu]
  let a : ℂ → ℝ := fun u => ((dloc u : ℤ) : ℝ) * (‖w - u‖ : ℝ)⁻¹
  let b : ℂ → ℝ := fun u => ((dg u : ℤ) : ℝ) * (if ‖u - w‖ ≤ 1 then (‖u - w‖ : ℝ)⁻¹ else 0)
  have hcoeff' : ∀ u, a u = b u := by
    intro u; exact hcoeff u
  have hsub_a : Function.support a ⊆ (S : Set ℂ) := by
    intro u hu
    have hdne : dg u ≠ 0 := by
      intro hd0
      have ha_b : a u = b u := hcoeff u
      have hb0 : b u = 0 := by
        dsimp [b]
        simp [hd0]
      have : a u = 0 := by
        calc
          a u = b u := ha_b
          _ = 0 := hb0
      exact hu this
    exact hmemS hdne
  have hsub_b : Function.support b ⊆ (S : Set ℂ) := by
    intro u hu
    have hdne : dg u ≠ 0 := by
      intro hd0
      have : b u = 0 := by
        dsimp [b]
        simp [hd0]
      exact hu this
    exact hmemS hdne
  calc
    (∑ᶠ u : ℂ, a u) = ∑ u ∈ S, a u := finsum_eq_sum_of_support_subset a hsub_a
    _ = ∑ u ∈ S, b u := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hcoeff u
    _ = (∑ᶠ u : ℂ, b u) := (finsum_eq_sum_of_support_subset b hsub_b).symm

/-! ## The θ-integral of the divisor sum -/

/-! ## Interval integrability of the local divisor sum -/
end Commons.Analysis.Complex