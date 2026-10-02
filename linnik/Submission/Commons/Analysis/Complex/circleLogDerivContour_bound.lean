import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.Analysis.Complex.circleBallTheta_integral_inv_le
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
        have hgoal : ‖u‖ ≤ ρ + 1 := by nlinarith only [htri2, hwρ, hu]
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

/-- The circle integral of the local divisor sum is controlled by the zero count and the
gap hypothesis: each zero `u` (with multiplicity `m_u`) contributes at most
`(16/ρ)·|‖u‖−ρ|⁻¹ ≤ (16/ρ)·(log (R+2) + A)²`, and the total multiplicity is `≤ cz·(ρ+1)·ℓ(ρ+1)`. -/
lemma theta_divisor_integral_le (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (A cz : ℝ) (hA : 0 ≤ A) (hcz : 0 ≤ cz) {ρ R : ℝ}
    (hρ : 4 ≤ ρ) (hR : 2 ≤ R) (hRρ : R ≤ ρ)
    (hzc : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) (ρ + 1))) u : ℤ) : ℝ)) ≤
        cz * (ρ + 1) * (Real.log (ρ + 3) + A))
    (hgap : ∀ u : ℂ, f u = 0 → (Real.log (R + 2) + A) ^ 2 * |‖u‖ - ρ| ≥ 1) :
    (∫ θ : ℝ in 0..(2 * Real.pi),
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f
        (Metric.closedBall (_root_.circleMap 0 ρ θ) 1)) u : ℤ) : ℝ) *
        ((‖_root_.circleMap 0 ρ θ - u‖ : ℝ)⁻¹))) ≤
      (16 / ρ) * (cz * (ρ + 1) * (Real.log (ρ + 3) + A)) * ((Real.log (R + 2) + A) ^ 2) := by
  classical
  let dg : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) (ρ + 1)) u
  let hd : ℝ → ℝ := fun θ => (∑ᶠ u : ℂ,
    (((MeromorphicOn.divisor f (Metric.closedBall (_root_.circleMap 0 ρ θ) 1)) u : ℤ) : ℝ) *
      ((‖_root_.circleMap 0 ρ θ - u‖ : ℝ)⁻¹))
  have hfG : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) (ρ + 1)) :=
    analyticOnNhd_closedBall_of_differentiable hf _
  have hgFin : (Function.support dg).Finite := by
    dsimp [dg]
    exact divisor_support_finite_closedBall (f := f) (a := (0 : ℂ)) (ρ := ρ + 1) hfG
  let S : Finset ℂ := hgFin.toFinset
  have hmemS : ∀ {u : ℂ}, dg u ≠ 0 → u ∈ S := by
    intro u h; exact (hgFin.mem_toFinset).mpr h
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ2 : 2 ≤ ρ := by linarith
  have hLRpos : 0 < Real.log (R + 2) + A := by
    have h1 : 1 < R + 2 := by linarith
    have hlg : 0 < Real.log (R + 2) := Real.log_pos h1
    linarith
  have hLR2pos : 0 < (Real.log (R + 2) + A) ^ 2 := by positivity
  -- each pointwise term is the local sum over the circle point
  have hlocal : ∀ θ, hd θ = (∑ᶠ u : ℂ,
      (((dg u : ℤ) : ℝ) * (if ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1 then
        (‖u - _root_.circleMap 0 ρ θ‖ : ℝ)⁻¹ else 0))) := by
    intro θ
    dsimp [hd, dg]
    have hw : ‖_root_.circleMap 0 ρ θ‖ = ρ := norm_circleMap_ofReal hρ0 θ
    have hfAnU : AnalyticOnNhd ℂ f
        (Metric.closedBall (_root_.circleMap 0 ρ θ) 1 ∪ Metric.closedBall (0 : ℂ) (ρ + 1)) :=
      analyticOnNhd_closedBall_of_differentiable hf _
    exact localDivisor_eq_global f hw hfAnU
  -- pointwise: hd θ equals the finite sum over S of m_u * circleTheta u ρ θ
  have hpoint : ∀ θ, hd θ = ∑ u ∈ S, ((dg u : ℤ) : ℝ) * circleTheta u ρ θ := by
    intro θ
    let b : ℂ → ℝ := fun u => ((dg u : ℤ) : ℝ) *
      (if ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1 then (‖u - _root_.circleMap 0 ρ θ‖ : ℝ)⁻¹ else 0)
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
      hd θ = ∑ᶠ u : ℂ, b u := by
        rw [hlocal θ]
      _ = ∑ u ∈ S, b u := finsum_eq_sum_of_support_subset b hsub_b
      _ = ∑ u ∈ S, ((dg u : ℤ) : ℝ) * circleTheta u ρ θ := by
        refine Finset.sum_congr rfl ?_
        intro u hu
        simp [b, circleTheta]
  -- zeros and the gap bound
  have hzero : ∀ u : ℂ, dg u ≠ 0 → f u = 0 := by
    intro u hdu
    exact zero_of_divisor_ne_zero (a := (0 : ℂ)) (ρ := ρ + 1) hfG hdu
  have hdist_ge : ∀ u θ, |‖u‖ - ρ| ≤ ‖u - _root_.circleMap 0 ρ θ‖ :=
    dist_circle_ge hρ0
  have hgap_le : ∀ u : ℂ, dg u ≠ 0 → 1 ≤ (Real.log (R + 2) + A) ^ 2 * |‖u‖ - ρ| := by
    intro u hdu
    exact hgap u (hzero u hdu)
  have hgap_le' : ∀ u : ℂ, dg u ≠ 0 → 1 ≤ |‖u‖ - ρ| * (Real.log (R + 2) + A) ^ 2 := by
    intro u hdu
    have hg := hgap_le u hdu
    nlinarith only [hg, show (Real.log (R + 2) + A) ^ 2 * |‖u‖ - ρ| =
      |‖u‖ - ρ| * (Real.log (R + 2) + A) ^ 2 by ring]
  have hh_u : ∀ u : ℂ, dg u ≠ 0 → 0 < |‖u‖ - ρ| := by
    intro u hdu
    have hle : 1 / ((Real.log (R + 2) + A) ^ 2) ≤ |‖u‖ - ρ| :=
      (div_le_iff₀ hLR2pos).2 (hgap_le' u hdu)
    have h0 : 0 < 1 / ((Real.log (R + 2) + A) ^ 2) := by positivity
    exact lt_of_lt_of_le h0 hle
  -- integrability of each circleTheta
  have hinter : ∀ u ∈ S, IntervalIntegrable (fun θ : ℝ => circleTheta u ρ θ) volume 0 (2 * Real.pi) := by
    intro u huS
    have hdu : dg u ≠ 0 := by exact (hgFin.mem_toFinset).1 huS
    let η : ℝ := |‖u‖ - ρ|
    have hη0 : 0 < η := by dsimp [η]; exact hh_u u hdu
    have huθ : ∀ θ, η ≤ ‖u - _root_.circleMap 0 ρ θ‖ := by
      intro θ
      dsimp [η]
      exact hdist_ge u θ
    exact intervalIntegrable_circleTheta hη0 huθ (by norm_num) (le_rfl) (by positivity)
  -- equality of integrals
  have hint_sum : (∫ θ in 0..(2 * Real.pi), hd θ)
      = ∑ u ∈ S, (∫ θ in 0..(2 * Real.pi), ((dg u : ℤ) : ℝ) * circleTheta u ρ θ) := by
    calc
      (∫ θ in 0..(2 * Real.pi), hd θ)
          = ∫ θ in 0..(2 * Real.pi), (∑ u ∈ S, ((dg u : ℤ) : ℝ) * circleTheta u ρ θ) := by
            apply intervalIntegral.integral_congr
            intro θ hθ
            exact hpoint θ
      _ = ∑ u ∈ S, (∫ θ in 0..(2 * Real.pi), ((dg u : ℤ) : ℝ) * circleTheta u ρ θ) := by
            refine intervalIntegral.integral_finsetSum ?_
            intro u huS
            have hii := hinter u huS
            exact hii.const_mul ((dg u : ℤ) : ℝ)
  -- per-term bounds
  have hterm : ∀ u ∈ S,
      (∫ θ in 0..(2 * Real.pi), ((dg u : ℤ) : ℝ) * circleTheta u ρ θ) ≤
        ((dg u : ℤ) : ℝ) * ((16 / ρ) / |‖u‖ - ρ|) := by
    intro u huS
    have hdu : dg u ≠ 0 := (hgFin.mem_toFinset).1 huS
    let η : ℝ := |‖u‖ - ρ|
    have hη0 : 0 < η := by dsimp [η]; exact hh_u u hdu
    have hbt : (∫ θ in 0..(2 * Real.pi), circleTheta u ρ θ) ≤ (16 / ρ) / η := by
      exact circleBallTheta_integral_inv_le hρ2 hη0 (u := u) (by dsimp [η]; rfl)
    have hmu0 : 0 ≤ ((dg u : ℤ) : ℝ) := divisor_nonneg_on_closedBall hfG u
    calc
      (∫ θ in 0..(2 * Real.pi), ((dg u : ℤ) : ℝ) * circleTheta u ρ θ)
          = ((dg u : ℤ) : ℝ) * (∫ θ in 0..(2 * Real.pi), circleTheta u ρ θ) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ ((dg u : ℤ) : ℝ) * ((16 / ρ) / η) := mul_le_mul_of_nonneg_left hbt hmu0
  -- replace the per-zero distance by the gap inverse
  have htermLR : ∀ u ∈ S,
      ((dg u : ℤ) : ℝ) * ((16 / ρ) / |‖u‖ - ρ|) ≤
        ((dg u : ℤ) : ℝ) * ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) := by
    intro u huS
    have hdu : dg u ≠ 0 := (hgFin.mem_toFinset).1 huS
    have hmu0 : 0 ≤ ((dg u : ℤ) : ℝ) := divisor_nonneg_on_closedBall hfG u
    have hhpos : 0 < |‖u‖ - ρ| := hh_u u hdu
    have h1over : (|‖u‖ - ρ|)⁻¹ ≤ (Real.log (R + 2) + A) ^ 2 := by
      simpa using (div_le_iff₀ hhpos).2 (hgap_le u hdu)
    have h16 : 0 ≤ 16 / ρ := by positivity
    have hstep : ((16 / ρ) / |‖u‖ - ρ|) ≤ (16 / ρ) * (Real.log (R + 2) + A) ^ 2 := by
      calc
        (16 / ρ) / |‖u‖ - ρ| = (16 / ρ) * (|‖u‖ - ρ|)⁻¹ := by ring
        _ ≤ (16 / ρ) * (Real.log (R + 2) + A) ^ 2 := mul_le_mul_of_nonneg_left h1over h16
    exact mul_le_mul_of_nonneg_left hstep hmu0
  have hsum_b : (∑ u ∈ S, (∫ θ in 0..(2 * Real.pi), ((dg u : ℤ) : ℝ) * circleTheta u ρ θ))
      ≤ ∑ u ∈ S, ((dg u : ℤ) : ℝ) * ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) := by
    calc
      (∑ u ∈ S, (∫ θ in 0..(2 * Real.pi), ((dg u : ℤ) : ℝ) * circleTheta u ρ θ))
          ≤ ∑ u ∈ S, ((dg u : ℤ) : ℝ) * ((16 / ρ) / |‖u‖ - ρ|) := by
            exact Finset.sum_le_sum (fun u hu => hterm u hu)
      _ ≤ ∑ u ∈ S, ((dg u : ℤ) : ℝ) * ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) := by
            exact Finset.sum_le_sum (fun u hu => htermLR u hu)
  -- total multiplicity from hzc
  have hsubS : Function.support (fun u : ℂ => ((dg u : ℤ) : ℝ)) ⊆ (S : Set ℂ) := by
    intro u hu
    have hd : dg u ≠ 0 := by
      intro h0
      exact hu (by simp [h0])
    exact hmemS hd
  have hfin_eq : (∑ᶠ u : ℂ, ((dg u : ℤ) : ℝ)) = ∑ u ∈ S, ((dg u : ℤ) : ℝ) :=
    finsum_eq_sum_of_support_subset (fun u : ℂ => ((dg u : ℤ) : ℝ)) hsubS
  have hzcS : (∑ u ∈ S, ((dg u : ℤ) : ℝ)) ≤ cz * (ρ + 1) * (Real.log (ρ + 3) + A) := by
    simpa [dg, hfin_eq] using hzc
  have hfac : (∑ u ∈ S, ((dg u : ℤ) : ℝ) * ((16 / ρ) * (Real.log (R + 2) + A) ^ 2))
      = ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) * (∑ u ∈ S, ((dg u : ℤ) : ℝ)) := by
    calc
      (∑ u ∈ S, ((dg u : ℤ) : ℝ) * ((16 / ρ) * (Real.log (R + 2) + A) ^ 2))
          = (∑ u ∈ S, ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) * ((dg u : ℤ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro u hu
            ring
      _ = ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) * (∑ u ∈ S, ((dg u : ℤ) : ℝ)) := by
            rw [Finset.mul_sum]
  have hposfac : 0 ≤ (16 / ρ) * (Real.log (R + 2) + A) ^ 2 := by positivity
  calc
    (∫ θ in 0..(2 * Real.pi), hd θ)
        = ∑ u ∈ S, (∫ θ in 0..(2 * Real.pi), ((dg u : ℤ) : ℝ) * circleTheta u ρ θ) := hint_sum
    _ ≤ ∑ u ∈ S, ((dg u : ℤ) : ℝ) * ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) := hsum_b
    _ = ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) * (∑ u ∈ S, ((dg u : ℤ) : ℝ)) := hfac
    _ ≤ ((16 / ρ) * (Real.log (R + 2) + A) ^ 2) * (cz * (ρ + 1) * (Real.log (ρ + 3) + A)) :=
          mul_le_mul_of_nonneg_left hzcS hposfac
    _ = (16 / ρ) * (cz * (ρ + 1) * (Real.log (ρ + 3) + A)) * ((Real.log (R + 2) + A) ^ 2) := by ring

/-! ## Interval integrability of the local divisor sum -/
lemma theta_divisor_integrable (f : ℂ → ℂ) (hf : Differentiable ℂ f) {ρ : ℝ} (hρ : 4 ≤ ρ)
    (hcircnz : ∀ w : ℂ, ‖w‖ = ρ → f w ≠ 0) :
    IntervalIntegrable (fun θ : ℝ => (∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor f (Metric.closedBall (_root_.circleMap 0 ρ θ) 1)) u : ℤ) : ℝ) *
        ((‖_root_.circleMap 0 ρ θ - u‖ : ℝ)⁻¹))) volume 0 (2 * Real.pi) := by
  classical
  let dg : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) (ρ + 1)) u
  let D : ℝ → ℝ := fun θ => (∑ᶠ u : ℂ,
    (((MeromorphicOn.divisor f (Metric.closedBall (_root_.circleMap 0 ρ θ) 1)) u : ℤ) : ℝ) *
      ((‖_root_.circleMap 0 ρ θ - u‖ : ℝ)⁻¹))
  have hfG : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) (ρ + 1)) :=
    analyticOnNhd_closedBall_of_differentiable hf _
  have hgFin : (Function.support dg).Finite := by
    dsimp [dg]
    exact divisor_support_finite_closedBall (f := f) (a := (0 : ℂ)) (ρ := ρ + 1) hfG
  let S : Finset ℂ := hgFin.toFinset
  have hmemS : ∀ {u : ℂ}, dg u ≠ 0 → u ∈ S := by
    intro u h; exact (hgFin.mem_toFinset).mpr h
  have hρ0 : 0 ≤ ρ := by linarith
  have hzero : ∀ u : ℂ, dg u ≠ 0 → f u = 0 := by
    intro u hdu
    exact zero_of_divisor_ne_zero (a := (0 : ℂ)) (ρ := ρ + 1) hfG hdu
  have hdist_ge : ∀ u θ, |‖u‖ - ρ| ≤ ‖u - _root_.circleMap 0 ρ θ‖ :=
    dist_circle_ge hρ0
  have hh_u : ∀ u : ℂ, dg u ≠ 0 → 0 < |‖u‖ - ρ| := by
    intro u hdu
    by_contra hz
    have hle : |‖u‖ - ρ| ≤ 0 := le_of_not_gt hz
    have habs : |‖u‖ - ρ| = 0 := le_antisymm hle (abs_nonneg _)
    have hnorm : ‖u‖ = ρ := by
      have : ‖u‖ - ρ = 0 := abs_eq_zero.mp habs
      linarith
    exact hcircnz u hnorm (hzero u hdu)
  -- pointwise equality with the finite sum over S
  have hlocal : ∀ θ, D θ = (∑ᶠ u : ℂ,
      (((dg u : ℤ) : ℝ) * (if ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1 then
        (‖u - _root_.circleMap 0 ρ θ‖ : ℝ)⁻¹ else 0))) := by
    intro θ
    dsimp [D, dg]
    have hw : ‖_root_.circleMap 0 ρ θ‖ = ρ := norm_circleMap_ofReal hρ0 θ
    have hfAnU : AnalyticOnNhd ℂ f
        (Metric.closedBall (_root_.circleMap 0 ρ θ) 1 ∪ Metric.closedBall (0 : ℂ) (ρ + 1)) :=
      analyticOnNhd_closedBall_of_differentiable hf _
    exact localDivisor_eq_global f hw hfAnU
  have hpoint : ∀ θ, D θ = ∑ u ∈ S, ((dg u : ℤ) : ℝ) * circleTheta u ρ θ := by
    intro θ
    let b : ℂ → ℝ := fun u => ((dg u : ℤ) : ℝ) *
      (if ‖u - _root_.circleMap 0 ρ θ‖ ≤ 1 then (‖u - _root_.circleMap 0 ρ θ‖ : ℝ)⁻¹ else 0)
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
      D θ = ∑ᶠ u : ℂ, b u := by
        rw [hlocal θ]
      _ = ∑ u ∈ S, b u := finsum_eq_sum_of_support_subset b hsub_b
      _ = ∑ u ∈ S, ((dg u : ℤ) : ℝ) * circleTheta u ρ θ := by
        refine Finset.sum_congr rfl ?_
        intro u hu
        simp [b, circleTheta]
  -- each circleTheta summand is interval integrable
  have hterm_int : ∀ u ∈ S, IntervalIntegrable (fun θ : ℝ => circleTheta u ρ θ) volume 0 (2 * Real.pi) := by
    intro u huS
    have hdu : dg u ≠ 0 := (hgFin.mem_toFinset).1 huS
    let η : ℝ := |‖u‖ - ρ|
    have hη0 : 0 < η := by dsimp [η]; exact hh_u u hdu
    have huθ : ∀ θ, η ≤ ‖u - _root_.circleMap 0 ρ θ‖ := by
      intro θ
      dsimp [η]
      exact hdist_ge u θ
    exact intervalIntegrable_circleTheta hη0 huθ (by norm_num) (le_rfl) (by positivity)
  have hfun : (fun θ : ℝ => ∑ u ∈ S, ((dg u : ℤ) : ℝ) * circleTheta u ρ θ)
      = (∑ u ∈ S, fun θ : ℝ => ((dg u : ℤ) : ℝ) * circleTheta u ρ θ) := by
    funext θ
    rw [Finset.sum_apply]
  have hsum_int' : IntervalIntegrable
      (∑ u ∈ S, fun θ : ℝ => ((dg u : ℤ) : ℝ) * circleTheta u ρ θ) volume 0 (2 * Real.pi) := by
    exact IntervalIntegrable.sum S
      (fun u hu => (hterm_int u hu).const_mul ((dg u : ℤ) : ℝ))
  have hsum_int : IntervalIntegrable (fun θ : ℝ => ∑ u ∈ S, ((dg u : ℤ) : ℝ) * circleTheta u ρ θ)
      volume 0 (2 * Real.pi) := by
    simpa [hfun] using hsum_int'
  -- rewrite: D is pointwise equal to the sum, hence integrable
  have hcongr : EqOn D (fun θ : ℝ => ∑ u ∈ S, ((dg u : ℤ) : ℝ) * circleTheta u ρ θ)
      (uIoc 0 (2 * Real.pi)) := by
    intro θ hθ
    exact hpoint θ
  have hDint : IntervalIntegrable D volume 0 (2 * Real.pi) :=
    (intervalIntegrable_congr hcongr).2 hsum_int
  simpa [D] using hDint

theorem circleLogDerivContour_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (s : ℂ) (A cp cz : ℝ) (hA : 0 ≤ A) (hcp : 0 ≤ cp) (hcz : 0 ≤ cz) {ρ R : ℝ}
    (hρ : 4 ≤ ρ) (hR : 2 ≤ R) (hRρ : R ≤ ρ) (hs : ‖s‖ ≤ ρ / 2)
    (hLDE : ∀ w : ℂ, ‖w‖ = ρ → f w ≠ 0 →
      ‖deriv f w / f w‖ ≤ cp * (Real.log (ρ + 2) + A) ^ 2 +
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹)))
    (hzc : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) (ρ + 1))) u : ℤ) : ℝ)) ≤
        cz * (ρ + 1) * (Real.log (ρ + 3) + A))
    (hgap : ∀ u : ℂ, f u = 0 → (Real.log (R + 2) + A) ^ 2 * |‖u‖ - ρ| ≥ 1)
    (hcircnz : ∀ w : ℂ, ‖w‖ = ρ → f w ≠ 0) :
    ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral (fun w : ℂ => (deriv f w / f w) * (1 / (s - w) - 1 / ((0 : ℂ) - w))) 0 ρ)‖ ≤
      ((4 * cp + 128 * cz + 1) * ‖s‖) * (Real.log (ρ + 2) + A) ^ 3 / ρ := by
  classical
  let wθ : ℝ → ℂ := fun θ => _root_.circleMap 0 ρ θ
  let L : ℝ := Real.log (ρ + 2) + A
  let Lp1 : ℝ := Real.log (ρ + 3) + A
  let LR : ℝ := Real.log (R + 2) + A
  let kern (w : ℂ) : ℂ := 1 / (s - w) - 1 / ((0 : ℂ) - w)
  let integ : ℂ → ℂ := fun w => (deriv f w / f w) * kern w
  let Dθ : ℝ → ℝ := fun θ => (∑ᶠ u : ℂ,
    (((MeromorphicOn.divisor f (Metric.closedBall (wθ θ) 1)) u : ℤ) : ℝ) * ((‖wθ θ - u‖ : ℝ)⁻¹))
  let n : ℝ := ‖s‖
  let K : ℝ := n / (ρ * (ρ - n))
  let C : ℝ := 16 / Real.pi
  have hρ0 : 0 ≤ ρ := by linarith
  have hρpos : 0 < ρ := by linarith
  have hρ2 : 2 ≤ ρ := by linarith
  have hn0 : 0 ≤ n := by dsimp [n]; exact norm_nonneg s
  have hsw : n < ρ := by dsimp [n]; nlinarith [hs]
  have hgeom : ρ / 2 ≤ ρ - n := by dsimp [n]; nlinarith only [hs]
  have hρnpos : 0 < ρ - n := by dsimp [n]; nlinarith [hs]
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hden_pos : 0 < ρ * (ρ - n) := by
    dsimp [n]
    positivity
  have hL1 : 1 ≤ L := by
    dsimp [L]
    have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have he4 : Real.exp 1 ≤ ρ + 2 := by
      have h4 : 4 ≤ ρ + 2 := by linarith
      exact le_trans (le_of_lt (lt_trans he3 (by norm_num : (3 : ℝ) < 4))) h4
    have hpos2 : 0 < ρ + 2 := by linarith
    have hlg : 1 ≤ Real.log (ρ + 2) := (Real.le_log_iff_exp_le hpos2).2 he4
    linarith
  have hLpos : 0 < L := by linarith
  have hLp1_nonneg : 0 ≤ Lp1 := by
    dsimp [Lp1]
    have h1 : 1 ≤ ρ + 3 := by linarith
    have hlg : 0 ≤ Real.log (ρ + 3) := Real.log_nonneg h1
    linarith
  have hLp1_le_2L : Lp1 ≤ 2 * L := by
    dsimp [Lp1, L]
    have hρ1 : 1 ≤ ρ := by linarith
    have hpos : 0 < ρ + 3 := by linarith
    have hsq : ρ + 3 ≤ (ρ + 2) ^ 2 := by nlinarith only [sq_nonneg ρ, hρ]
    have hlg : Real.log (ρ + 3) ≤ 2 * Real.log (ρ + 2) := by
      have h1 := Real.log_le_log hpos hsq
      rw [Real.log_pow (ρ + 2) 2] at h1
      norm_num at h1
      exact h1
    have hA0 : 0 ≤ A := hA
    nlinarith
  have hLR_le_L : LR ≤ L := by
    dsimp [LR, L]
    have h1 : 0 < R + 2 := by linarith
    have h2 : R + 2 ≤ ρ + 2 := by linarith
    have hlg : Real.log (R + 2) ≤ Real.log (ρ + 2) := Real.log_le_log h1 h2
    linarith
  have hLR2_le_L2 : LR ^ 2 ≤ L ^ 2 := by
    have hLR0 : 0 ≤ LR := by
      dsimp [LR]
      have h1 : 1 ≤ R + 2 := by linarith
      have hlg : 0 ≤ Real.log (R + 2) := Real.log_nonneg h1
      linarith
    have hL0 : 0 ≤ L := by linarith
    exact pow_le_pow_left₀ hLR0 hLR_le_L 2
  have hC_le : C ≤ 16 := by
    dsimp [C]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
    nlinarith only [Real.pi_gt_three]
  have hC_pos : 0 < C := by dsimp [C]; positivity
  have hρp1_le : ρ + 1 ≤ 2 * ρ := by nlinarith only [hρ]
  -- the circle point
  have hwθ : ∀ θ, ‖wθ θ‖ = ρ := by
    intro θ
    dsimp [wθ]
    exact norm_circleMap_ofReal hρ0 θ
  -- interval integrability and nonnegativity of the divisor sum along the circle
  have hDθint : IntervalIntegrable (fun θ : ℝ => Dθ θ) volume 0 (2 * Real.pi) := by
    have h := theta_divisor_integrable f hf hρ hcircnz
    simpa [Dθ, wθ] using h
  have hDnonneg : ∀ θ, 0 ≤ Dθ θ := by
    intro θ
    dsimp [Dθ]
    apply finsum_nonneg
    intro u
    have hlocAn : AnalyticOnNhd ℂ f (Metric.closedBall (wθ θ) 1) :=
      analyticOnNhd_closedBall_of_differentiable hf _
    have hmu0 : 0 ≤ (((MeromorphicOn.divisor f (Metric.closedBall (wθ θ) 1)) u : ℤ) : ℝ) :=
      divisor_nonneg_on_closedBall hlocAn u
    have hinv0 : 0 ≤ (‖wθ θ - u‖ : ℝ)⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    exact mul_nonneg hmu0 hinv0
  have hzeroInt : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 (2 * Real.pi) := by
    simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
      volume 0 (2 * Real.pi))
  have hDnonneg0 : (fun _ : ℝ => (0 : ℝ)) ≤ Dθ := by
    intro θ
    exact hDnonneg θ
  have hJD0 : 0 ≤ (∫ θ in 0..(2 * Real.pi), Dθ θ) := by
    have hmono := intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      hzeroInt hDθint hDnonneg0
    simpa using hmono
  -- the kernel factor
  have hkernel : ∀ θ, ‖kern (wθ θ)‖ ≤ K := by
    intro θ
    have hb := kernel_abs_le hρpos (by simpa [n] using hsw) (hwθ θ)
    simpa [kern, K, n, wθ] using hb
  -- pointwise log-derivative bound
  have hld : ∀ θ, ‖deriv f (wθ θ) / f (wθ θ)‖ ≤ cp * L ^ 2 + Dθ θ := by
    intro θ
    have hnz : f (wθ θ) ≠ 0 := hcircnz (wθ θ) (hwθ θ)
    have hb := hLDE (wθ θ) (hwθ θ) hnz
    simpa [L, Dθ, wθ] using hb
  -- pointwise norm of the integrand
  have hnormpt : ∀ θ, ‖integ (wθ θ)‖ ≤ (cp * L ^ 2 + Dθ θ) * K := by
    intro θ
    have hLp : 0 ≤ cp * L ^ 2 + Dθ θ := by
      have h1 : 0 ≤ cp * L ^ 2 := mul_nonneg hcp (sq_nonneg L)
      linarith [hDnonneg θ]
    calc
      ‖integ (wθ θ)‖ = ‖(deriv f (wθ θ) / f (wθ θ)) * kern (wθ θ)‖ := by
        rfl
      _ ≤ ‖deriv f (wθ θ) / f (wθ θ)‖ * ‖kern (wθ θ)‖ := norm_mul_le _ _
      _ ≤ (cp * L ^ 2 + Dθ θ) * ‖kern (wθ θ)‖ := by
        exact mul_le_mul_of_nonneg_right (hld θ) (norm_nonneg _)
      _ ≤ (cp * L ^ 2 + Dθ θ) * K := by
        exact mul_le_mul_of_nonneg_left (hkernel θ) hLp
  -- integrability and nonnegativity of the pointwise upper bound
  let F : ℝ → ℝ := fun θ => (cp * L ^ 2 + Dθ θ) * K
  have hFint : IntervalIntegrable F volume 0 (2 * Real.pi) := by
    have hcst : IntervalIntegrable (fun _ : ℝ => cp * L ^ 2) volume 0 (2 * Real.pi) := by
      simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => cp * L ^ 2)
        volume 0 (2 * Real.pi))
    have hsumI : IntervalIntegrable (fun θ : ℝ => cp * L ^ 2 + Dθ θ) volume 0 (2 * Real.pi) := by
      have h := hcst.add hDθint
      simpa using h
    have hm := hsumI.mul_const K
    simpa [F] using hm
  have hFnonneg : ∀ θ, 0 ≤ F θ := by
    intro θ
    dsimp [F]
    have h1 : 0 ≤ cp * L ^ 2 := mul_nonneg hcp (sq_nonneg L)
    exact mul_nonneg (by linarith [hDnonneg θ]) hK0
  -- integral of the pointwise sum splits
  have hJsum : (∫ θ in 0..(2 * Real.pi), (cp * L ^ 2 + Dθ θ)) =
      cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ) := by
    have hcst : IntervalIntegrable (fun _ : ℝ => cp * L ^ 2) volume 0 (2 * Real.pi) := by
      simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => cp * L ^ 2)
        volume 0 (2 * Real.pi))
    calc
      (∫ θ in 0..(2 * Real.pi), (cp * L ^ 2 + Dθ θ))
          = (∫ θ in 0..(2 * Real.pi), ((fun _ : ℝ => cp * L ^ 2) θ + Dθ θ)) := by
            apply intervalIntegral.integral_congr
            intro θ hθ
            rfl
      _ = (∫ θ in 0..(2 * Real.pi), (fun _ : ℝ => cp * L ^ 2) θ) +
          (∫ θ in 0..(2 * Real.pi), Dθ θ) := by
            rw [intervalIntegral.integral_add hcst hDθint]
      _ = cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ) := by
            have hc : (∫ θ in 0..(2 * Real.pi), (fun _ : ℝ => cp * L ^ 2) θ) =
                cp * L ^ 2 * (2 * Real.pi) := by
              rw [intervalIntegral.integral_const]
              simp [smul_eq_mul]
              ring
            rw [hc]
  -- the circle-integral estimate
  have hG1 : ‖circleIntegral integ 0 ρ‖ ≤ ρ * (∫ θ in 0..(2 * Real.pi), ‖integ (wθ θ)‖) := by
    simpa [wθ] using (circleIntegral_norm_le hρ0 (f := integ))
  have hG2 : (∫ θ in 0..(2 * Real.pi), ‖integ (wθ θ)‖) ≤
      (∫ θ in 0..(2 * Real.pi), F θ) := by
    by_cases hii : IntervalIntegrable (fun θ : ℝ => ‖integ (wθ θ)‖) volume 0 (2 * Real.pi)
    · have hpt0 : (fun θ : ℝ => ‖integ (wθ θ)‖) ≤ F := by
        intro θ
        simpa [F] using hnormpt θ
      exact intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hii hFint hpt0
    · have hz : (∫ θ in 0..(2 * Real.pi), ‖integ (wθ θ)‖) = 0 :=
        intervalIntegral.integral_undef hii
      have hge0 : 0 ≤ (∫ θ in 0..(2 * Real.pi), F θ) := by
        refine intervalIntegral.integral_nonneg_of_ae (by positivity : (0 : ℝ) ≤ 2 * Real.pi) ?_
        apply Filter.Eventually.of_forall
        exact hFnonneg
      rw [hz]
      exact hge0
  have hsplit : (∫ θ in 0..(2 * Real.pi), F θ) =
      (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) * K := by
    calc
      (∫ θ in 0..(2 * Real.pi), F θ)
          = ((∫ θ in 0..(2 * Real.pi), (cp * L ^ 2 + Dθ θ))) * K := by
            dsimp [F]
            rw [intervalIntegral.integral_mul_const]
      _ = (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) * K := by
            rw [hJsum]
  have hρK : ρ * K = n / (ρ - n) := by
    dsimp [K]
    field_simp [hρpos.ne', hρnpos.ne']
  have hG3eq : ρ * (∫ θ in 0..(2 * Real.pi), F θ) =
      (n / (ρ - n)) * (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) := by
    calc
      ρ * (∫ θ in 0..(2 * Real.pi), F θ)
          = ((cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) * K) * ρ := by
            rw [hsplit]
            ring
      _ = (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) * (ρ * K) := by
            ring
      _ = (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) * (n / (ρ - n)) := by
            rw [hρK]
      _ = (n / (ρ - n)) * (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) := by
            ring
  have hG3 : ρ * (∫ θ in 0..(2 * Real.pi), F θ) ≤
      (n / (ρ - n)) * (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) := by
    exact le_of_eq hG3eq
  have hG : ‖circleIntegral integ 0 ρ‖ ≤
      (n / (ρ - n)) * (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) := by
    calc
      ‖circleIntegral integ 0 ρ‖ ≤ ρ * (∫ θ in 0..(2 * Real.pi), ‖integ (wθ θ)‖) := hG1
      _ ≤ ρ * (∫ θ in 0..(2 * Real.pi), F θ) := by
            exact mul_le_mul_of_nonneg_left hG2 hρ0
      _ ≤ (n / (ρ - n)) * (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ)) := hG3
  have h2p0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hmain0 : ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) • circleIntegral integ 0 ρ)‖ ≤
      n * cp * L ^ 2 / (ρ - n) +
        n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n)) := by
    have hscaled : ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) • circleIntegral integ 0 ρ)‖ ≤
        (1 / (2 * Real.pi)) * ‖circleIntegral integ 0 ρ‖ :=
      norm_scaled_circle_le (circleIntegral integ 0 ρ)
    calc
      ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) • circleIntegral integ 0 ρ)‖
          ≤ (1 / (2 * Real.pi)) * ‖circleIntegral integ 0 ρ‖ := hscaled
      _ ≤ (1 / (2 * Real.pi)) * ((n / (ρ - n)) *
            (cp * L ^ 2 * (2 * Real.pi) + (∫ θ in 0..(2 * Real.pi), Dθ θ))) := by
            exact mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
      _ = n * cp * L ^ 2 / (ρ - n) +
            n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n)) := by
            field_simp [hρnpos.ne', h2p0]
  -- bound the cp part
  have hbnd1 : n * cp * L ^ 2 / (ρ - n) ≤ 2 * cp * n * L ^ 2 / ρ := by
    have h12 : 1 / (ρ - n) ≤ 2 / ρ := by
      rw [div_le_div_iff₀ hρnpos hρpos]
      dsimp [n]
      nlinarith only [hs]
    have hm0 : 0 ≤ n * cp * L ^ 2 := by positivity
    calc
      n * cp * L ^ 2 / (ρ - n) = (n * cp * L ^ 2) * (1 / (ρ - n)) := by ring
      _ ≤ (n * cp * L ^ 2) * (2 / ρ) := mul_le_mul_of_nonneg_left h12 hm0
      _ = 2 * cp * n * L ^ 2 / ρ := by ring
  -- bound the divisor part
  have hDθb : (∫ θ in 0..(2 * Real.pi), Dθ θ) ≤ (16 / ρ) * (cz * (ρ + 1) * Lp1) * (LR ^ 2) := by
    have h := theta_divisor_integral_le f hf A cz hA hcz hρ hR hRρ hzc hgap
    simpa [Dθ, wθ, Lp1, LR] using h
  have hbnd2 : n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n)) ≤
      C * cz * n * (ρ + 1) * Lp1 * L ^ 2 / ρ ^ 2 := by
    have hden : 1 / (2 * Real.pi * (ρ - n)) ≤ 1 / (Real.pi * ρ) := by
      rw [div_le_div_iff₀]
      · have hX : ρ ≤ 2 * (ρ - n) := by dsimp [n]; nlinarith only [hs]
        nlinarith only [mul_le_mul_of_nonneg_left hX Real.pi_pos.le]
      · positivity
      · positivity
    have hm : 0 ≤ n * (∫ θ in 0..(2 * Real.pi), Dθ θ) := by
      exact mul_nonneg hn0 hJD0
    have hstep1 : n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n)) ≤
        n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (Real.pi * ρ) := by
      calc
        n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n))
            = (n * (∫ θ in 0..(2 * Real.pi), Dθ θ)) * (1 / (2 * Real.pi * (ρ - n))) := by ring
        _ ≤ (n * (∫ θ in 0..(2 * Real.pi), Dθ θ)) * (1 / (Real.pi * ρ)) :=
              mul_le_mul_of_nonneg_left hden hm
        _ = n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (Real.pi * ρ) := by ring
    have hstep2 : n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (Real.pi * ρ) ≤
        n * ((16 / ρ) * (cz * (ρ + 1) * Lp1) * (LR ^ 2)) / (Real.pi * ρ) := by
      have h1 : n * (∫ θ in 0..(2 * Real.pi), Dθ θ) ≤
          n * ((16 / ρ) * (cz * (ρ + 1) * Lp1) * (LR ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hDθb hn0
      exact div_le_div_of_nonneg_right h1 (by positivity : 0 ≤ Real.pi * ρ)
    have hstep3 : n * ((16 / ρ) * (cz * (ρ + 1) * Lp1) * (LR ^ 2)) / (Real.pi * ρ) =
        C * cz * n * (ρ + 1) * Lp1 * (LR ^ 2) / ρ ^ 2 := by
      dsimp [C]
      field_simp [hρpos.ne', (by positivity : Real.pi ≠ 0)]
    calc
      n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n)) ≤
          n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (Real.pi * ρ) := hstep1
      _ ≤ n * ((16 / ρ) * (cz * (ρ + 1) * Lp1) * (LR ^ 2)) / (Real.pi * ρ) := hstep2
      _ = C * cz * n * (ρ + 1) * Lp1 * (LR ^ 2) / ρ ^ 2 := hstep3
      _ ≤ C * cz * n * (ρ + 1) * Lp1 * L ^ 2 / ρ ^ 2 := by
            have hm1 : 0 ≤ C * cz * n * (ρ + 1) * Lp1 := by positivity
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hLR2_le_L2 hm1)
              (by positivity : 0 ≤ ρ ^ 2)
  -- final real inequality
  have hfin0 : 2 * cp * n * L ^ 2 / ρ +
        C * cz * n * (ρ + 1) * Lp1 * L ^ 2 / ρ ^ 2 ≤
      ((4 * cp + 128 * cz + 1) * n) * L ^ 3 / ρ := by
    have hCr : C * (ρ + 1) * Lp1 ≤ 128 * L * ρ := by
      have hA1 : C * (ρ + 1) ≤ 16 * (2 * ρ) := by
        have hC0 : 0 ≤ C := hC_pos.le
        exact mul_le_mul hC_le hρp1_le (by linarith : 0 ≤ ρ + 1) (by norm_num)
      have hA2 : 16 * (2 * ρ) * Lp1 ≤ 16 * (2 * ρ) * (2 * L) := by
        exact mul_le_mul_of_nonneg_left hLp1_le_2L (by positivity : 0 ≤ 16 * (2 * ρ))
      have hA3 : 16 * (2 * ρ) * (2 * L) ≤ 128 * L * ρ := by
        have hρL0 : 0 ≤ ρ * L := mul_nonneg hρ0 (le_of_lt hLpos)
        nlinarith only [hρL0]
      calc
        C * (ρ + 1) * Lp1 = (C * (ρ + 1)) * Lp1 := by ring
        _ ≤ (16 * (2 * ρ)) * Lp1 := by
              exact mul_le_mul_of_nonneg_right hA1 hLp1_nonneg
        _ ≤ (16 * (2 * ρ)) * (2 * L) := hA2
        _ ≤ 128 * L * ρ := hA3
    have hP1 : 2 * cp * n * L ^ 2 * ρ ≤ 4 * cp * n * L ^ 3 * ρ := by
      have hfac : 0 ≤ cp * n * L ^ 2 * ρ := by positivity
      calc
        2 * cp * n * L ^ 2 * ρ = (2 : ℝ) * (cp * n * L ^ 2 * ρ) := by ring
        _ ≤ (4 * L) * (cp * n * L ^ 2 * ρ) := by
              exact mul_le_mul_of_nonneg_right (by nlinarith only [hL1]) hfac
        _ = 4 * cp * n * L ^ 3 * ρ := by ring
    have hmul0 : 0 ≤ cz * n * L ^ 2 := by positivity
    have hP2 : C * cz * n * (ρ + 1) * Lp1 * L ^ 2 ≤ 128 * cz * n * L ^ 3 * ρ := by
      have hstep := mul_le_mul_of_nonneg_right hCr hmul0
      nlinarith only [hstep]
    have hN : 0 ≤ n * L ^ 3 * ρ := by positivity
    -- multiply the goal inequality by ρ ^ 2 > 0 and prove
    have hρ2pos : 0 < ρ ^ 2 := by positivity
    have hnum : 2 * cp * n * L ^ 2 * ρ + C * cz * n * (ρ + 1) * Lp1 * L ^ 2 ≤
        (4 * cp + 128 * cz + 1) * n * L ^ 3 * ρ := by
      nlinarith only [hP1, hP2, hN]
    calc
      2 * cp * n * L ^ 2 / ρ + C * cz * n * (ρ + 1) * Lp1 * L ^ 2 / ρ ^ 2
          = (2 * cp * n * L ^ 2 * ρ + C * cz * n * (ρ + 1) * Lp1 * L ^ 2) / ρ ^ 2 := by
            field_simp [hρpos.ne']
      _ ≤ ((4 * cp + 128 * cz + 1) * n * L ^ 3 * ρ) / ρ ^ 2 := by
            exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ ρ ^ 2)
      _ = ((4 * cp + 128 * cz + 1) * n) * L ^ 3 / ρ := by
            field_simp [hρpos.ne']
  -- assemble
  calc
    ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral integ 0 ρ)‖
        ≤ n * cp * L ^ 2 / (ρ - n) +
            n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n)) := hmain0
    _ ≤ 2 * cp * n * L ^ 2 / ρ +
            n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hbnd1 (n * (∫ θ in 0..(2 * Real.pi), Dθ θ) / (2 * Real.pi * (ρ - n)))
    _ ≤ 2 * cp * n * L ^ 2 / ρ +
            C * cz * n * (ρ + 1) * Lp1 * L ^ 2 / ρ ^ 2 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hbnd2 (2 * cp * n * L ^ 2 / ρ)
    _ ≤ ((4 * cp + 128 * cz + 1) * n) * L ^ 3 / ρ := hfin0
    _ = ((4 * cp + 128 * cz + 1) * ‖s‖) * (Real.log (ρ + 2) + A) ^ 3 / ρ := by
          dsimp [n, L]

end Commons.Analysis.Complex