/-
# `Work.FTS.BSSwirl.residualIntegralBound` — the integral estimate for the Newtonian residual

The core measure-theoretic estimate of `Work.FTS.BSSwirl.hasFDerivAt_newtonPotential`:

  `‖∫ y, K(h,y) • ω y‖ ≤ M (34π‖h‖² + 80000π√(|R|+‖x‖+1)‖h‖^{3/2})`

for `K(h,y) = ‖(x+h)-y‖⁻¹ - ‖x-y‖⁻¹ + ‖x-y‖⁻³⟪x-y,h⟫`, `ω` bounded by `M`, supported in
`B(0,R)` and ae-strongly-measurable.  The residual is bounded crudely on `{‖x-y‖ < 2‖h‖}` and by
the Taylor estimate `10000‖h‖^{3/2}‖x-y‖^{-5/2}` on the complement; the two pieces are integrated
with the shifted ball integrals `ball_lintegral_rpow_sub_le`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.NewtonPotentialAux
import Submission.Work.FTS.BSSwirl.ball_lintegral_rpow_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Set
open scoped Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## The integral estimate -/

/-- **The core estimate.**  For bounded, compactly supported, ae-strongly-measurable `ω`,

  `‖∫ y, K(h,y) • ω y‖ ≤ M (34π‖h‖² + 80000π√(|R|+‖x‖+1)‖h‖^{3/2})`,

where `K(h,y) = ‖(x+h)-y‖⁻¹ - ‖x-y‖⁻¹ + ‖x-y‖⁻³⟪x-y,h⟫`. -/
lemma residual_integral_bound {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) (x h : R3) :
    ‖∫ y, ((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y‖
      ≤ M * (34 * Real.pi * ‖h‖ ^ 2
              + 80000 * Real.pi * Real.sqrt (|R| + ‖x‖ + 1) * ‖h‖ ^ ((3 : ℝ) / 2)) := by
  classical
  rcases eq_or_ne h 0 with rfl | hne
  · have hzero : (fun y : R3 => ((‖(x + 0) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) (0 : R3)) • ω y)
        = fun _ : R3 => (0 : R3) := by
      funext y
      simp
    rw [hzero, integral_zero, norm_zero]
    positivity
  · set r : ℝ := ‖h‖ with hrr
    have hrpos : 0 < r := by rw [hrr]; exact norm_pos_iff.mpr hne
    have hrnn : 0 ≤ r := le_of_lt hrpos
    set D : ℝ := |R| + ‖x‖ + 1 with hDD
    have hDpos : 0 < D := by rw [hDD]; positivity
    set small : Set R3 := {y : R3 | ‖x - y‖ < 2 * r} with hsmall
    set far : Set R3 := {y : R3 | 2 * r ≤ ‖x - y‖} with hfarSet
    have hSmeas : MeasurableSet (Metric.closedBall (0 : R3) R) :=
      Metric.isClosed_closedBall.measurableSet
    have hcont : Continuous (fun y : R3 => ‖x - y‖) :=
      continuous_norm.comp (continuous_const.sub continuous_id)
    have hsmallmeas : MeasurableSet small := (isOpen_lt hcont continuous_const).measurableSet
    have hfarmeas : MeasurableSet far := (isClosed_le continuous_const hcont).measurableSet
    -- the far-regime pointwise bound, with `‖h‖` replaced by `r`
    have hfar : ∀ y : R3, 2 * r ≤ ‖x - y‖ → |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
        + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|
        ≤ 10000 * r ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2) := by
      intro y hy
      have := abs_residual_far x h y (by rw [← hrr]; exact hy)
      rwa [hrr]
    -- the pointwise comparison
    have hpt : ∀ y : R3, ENNReal.ofReal ‖((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y‖
        ≤ (Metric.closedBall (0 : R3) R ∩ small).indicator (fun y => ENNReal.ofReal
            (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹))) y
          + (Metric.closedBall (0 : R3) R ∩ far).indicator (fun y => ENNReal.ofReal
            (M * (10000 * r ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2)))) y := by
      intro y
      by_cases hy : y ∈ Metric.closedBall (0 : R3) R
      · have hle : ENNReal.ofReal ‖((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
            + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y‖
            ≤ ENNReal.ofReal (M * |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
              + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h|) := by
          apply ENNReal.ofReal_le_ofReal
          rw [norm_smul, Real.norm_eq_abs]
          calc |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
                + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h| * ‖ω y‖
              ≤ |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
                + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h| * M :=
                mul_le_mul_of_nonneg_left (hbdd y) (abs_nonneg _)
            _ = M * |(‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
                + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h| := by ring
        rcases lt_or_ge (‖x - y‖) (2 * r) with hs | hf
        · have hyfar : y ∉ far := by simp only [far, Set.mem_ofPred_eq]; linarith
          rw [Set.indicator_of_mem (show y ∈ Metric.closedBall (0 : R3) R ∩ small from
                ⟨hy, hs⟩),
            Set.indicator_of_notMem (show y ∉ Metric.closedBall (0 : R3) R ∩ far from
                fun hh => hyfar hh.2)]
          simpa using hle.trans (ENNReal.ofReal_le_ofReal
            (by have := abs_residual_crude x h y
                nlinarith [this, hM, abs_nonneg ((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
                  + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h)]))
        · have hynsmall : y ∉ small := by simp only [small, Set.mem_ofPred_eq]; exact not_lt.mpr hf
          rw [Set.indicator_of_notMem (show y ∉ Metric.closedBall (0 : R3) R ∩ small from
                fun hh => hynsmall hh.2),
            Set.indicator_of_mem (show y ∈ Metric.closedBall (0 : R3) R ∩ far from ⟨hy, hf⟩)]
          simpa using hle.trans (ENNReal.ofReal_le_ofReal
            (by have := hfar y hf
                nlinarith [this, hM, abs_nonneg ((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
                  + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h)]))
      · have hωy : ω y = 0 := by
          by_contra hh
          exact hy (hsupp y hh)
        rw [hωy, smul_zero, norm_zero, ENNReal.ofReal_zero]
        positivity
    -- measurability of the two indicator functions
    have hAmeas : AEMeasurable ((Metric.closedBall (0 : R3) R ∩ small).indicator
        (fun y => ENNReal.ofReal
          (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)))) volume := by
      have hm : Measurable (fun y : R3 => ENNReal.ofReal
          (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹))) := by
        measurability
      exact (hm.indicator (hSmeas.inter hsmallmeas)).aemeasurable
    have hstep1 : ∫⁻ y, ENNReal.ofReal ‖((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y‖
        ≤ (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
            (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)))
          + (∫⁻ y in Metric.closedBall (0 : R3) R ∩ far, ENNReal.ofReal
            (M * (10000 * r ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2)))) := by
      calc ∫⁻ y, ENNReal.ofReal ‖((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
            + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y‖
          ≤ ∫⁻ y, ((Metric.closedBall (0 : R3) R ∩ small).indicator (fun y => ENNReal.ofReal
                (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹
                  + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹))) y
              + (Metric.closedBall (0 : R3) R ∩ far).indicator (fun y => ENNReal.ofReal
                (M * (10000 * r ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2)))) y) :=
            lintegral_mono hpt
        _ = (∫⁻ y, (Metric.closedBall (0 : R3) R ∩ small).indicator (fun y => ENNReal.ofReal
                (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹
                  + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹))) y)
              + ∫⁻ y, (Metric.closedBall (0 : R3) R ∩ far).indicator (fun y => ENNReal.ofReal
                (M * (10000 * r ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2)))) y :=
            lintegral_add_left' hAmeas _
        _ = _ := by
            rw [lintegral_indicator (hSmeas.inter hsmallmeas),
              lintegral_indicator (hSmeas.inter hfarmeas)]
    -- the three small-region pieces
    have hsmall_bound : (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
          (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)))
        ≤ ENNReal.ofReal (M * (34 * Real.pi * r ^ 2)) := by
      have hsplit : (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
            (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)))
          ≤ (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
                (M * (‖(x + h) - y‖)⁻¹))
            + (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
                (M * (‖x - y‖)⁻¹))
            + (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
                (M * r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)) := by
        have hpt : ∀ y : R3, ENNReal.ofReal (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹
              + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹))
            ≤ ENNReal.ofReal (M * (‖(x + h) - y‖)⁻¹)
              + ENNReal.ofReal (M * (‖x - y‖)⁻¹)
              + ENNReal.ofReal (M * r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹) := by
          intro y
          rw [show M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹
                + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)
              = M * (‖(x + h) - y‖)⁻¹
                + (M * (‖x - y‖)⁻¹ + M * r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹) by ring,
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
          exact le_of_eq (add_assoc _ _ _).symm
        refine le_trans (lintegral_mono hpt) (le_of_eq ?_)
        rw [lintegral_add_right _ (by measurability)]
        rw [lintegral_add_right _ (by measurability)]
      -- three ball bounds
      have hB1 : (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
            (M * (‖(x + h) - y‖)⁻¹)) ≤ ENNReal.ofReal (M * (2 * Real.pi * (3 * r) ^ 2)) := by
        have hsub : Metric.closedBall (0 : R3) R ∩ small ⊆ Metric.ball (x + h) (3 * r) := by
          intro y hy
          obtain ⟨hyS, hys⟩ := hy
          change ‖x - y‖ < 2 * r at hys
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hyS
          rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev y (x + h)]
          calc ‖(x + h) - y‖ = ‖(x - y) + h‖ := by
                rw [show (x + h) - y = (x - y) + h from by abel]
            _ ≤ ‖x - y‖ + ‖h‖ := norm_add_le _ _
            _ < 2 * r + r := by rw [← hrr]; linarith
            _ = 3 * r := by ring
        have h3 : ∫⁻ y in Metric.ball (x + h) (3 * r), ENNReal.ofReal ((‖(x + h) - y‖)⁻¹)
            ≤ ENNReal.ofReal (2 * Real.pi * (3 * r) ^ 2) := by
          rw [show (fun y : R3 => ENNReal.ofReal ((‖(x + h) - y‖)⁻¹))
              = fun y : R3 => ENNReal.ofReal (‖(x + h) - y‖ ^ (-1 : ℝ)) from by
                funext y; rw [Real.rpow_neg_one]]
          refine (ball_lintegral_rpow_sub_le (s := -1) (by norm_num) (x + h) (ρ := 3 * r)
            (by linarith)).trans (le_of_eq ?_)
          rw [show (-1 : ℝ) + 3 = 2 by norm_num, Real.rpow_two]
          ring
        refine le_trans (lintegral_mono_set hsub) ?_
        rw [show (fun y : R3 => ENNReal.ofReal (M * (‖(x + h) - y‖)⁻¹))
            = fun y : R3 => ENNReal.ofReal M * ENNReal.ofReal ((‖(x + h) - y‖)⁻¹) from by
              funext y; rw [ENNReal.ofReal_mul hM]]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [ENNReal.ofReal_mul hM]
        exact mul_le_mul_right h3 (ENNReal.ofReal M)
      have hB2 : (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
            (M * (‖x - y‖)⁻¹)) ≤ ENNReal.ofReal (M * (2 * Real.pi * (2 * r) ^ 2)) := by
        have hsub : Metric.closedBall (0 : R3) R ∩ small ⊆ Metric.ball x (2 * r) := by
          intro y hy
          obtain ⟨_, hys⟩ := hy
          rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev y x]
          exact hys
        have h3 : ∫⁻ y in Metric.ball x (2 * r), ENNReal.ofReal ((‖x - y‖)⁻¹)
            ≤ ENNReal.ofReal (2 * Real.pi * (2 * r) ^ 2) := by
          rw [show (fun y : R3 => ENNReal.ofReal ((‖x - y‖)⁻¹))
              = fun y : R3 => ENNReal.ofReal (‖x - y‖ ^ (-1 : ℝ)) from by
                funext y; rw [Real.rpow_neg_one]]
          refine (ball_lintegral_rpow_sub_le (s := -1) (by norm_num) x (ρ := 2 * r)
            (by linarith)).trans (le_of_eq ?_)
          rw [show (-1 : ℝ) + 3 = 2 by norm_num, Real.rpow_two]
          ring
        refine le_trans (lintegral_mono_set hsub) ?_
        rw [show (fun y : R3 => ENNReal.ofReal (M * (‖x - y‖)⁻¹))
            = fun y : R3 => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖)⁻¹) from by
              funext y; rw [ENNReal.ofReal_mul hM]]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [ENNReal.ofReal_mul hM]
        exact mul_le_mul_right h3 (ENNReal.ofReal M)
      have hB3 : (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
            (M * r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹))
          ≤ ENNReal.ofReal (M * r * (4 * Real.pi * (2 * r))) := by
        have hsub : Metric.closedBall (0 : R3) R ∩ small ⊆ Metric.ball x (2 * r) := by
          intro y hy
          obtain ⟨_, hys⟩ := hy
          rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev y x]
          exact hys
        have h3 : ∫⁻ y in Metric.ball x (2 * r), ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)
            ≤ ENNReal.ofReal (4 * Real.pi * (2 * r)) := by
          rw [show (fun y : R3 => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹))
              = fun y : R3 => ENNReal.ofReal (‖x - y‖ ^ (-2 : ℝ)) from by
                funext y
                rw [inv_natPow_eq_rpow_neg' (norm_nonneg (x - y)) 2]
                norm_num]
          refine (ball_lintegral_rpow_sub_le (s := -2) (by norm_num) x (ρ := 2 * r)
            (by linarith)).trans (le_of_eq ?_)
          rw [show (-2 : ℝ) + 3 = 1 by norm_num, Real.rpow_one]
          ring
        refine le_trans (lintegral_mono_set hsub) ?_
        rw [show (fun y : R3 => ENNReal.ofReal (M * r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹))
            = fun y : R3 => ENNReal.ofReal (M * r) * ENNReal.ofReal
                ((‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹) from by
              funext y; rw [ENNReal.ofReal_mul (by positivity)]]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [show ENNReal.ofReal (M * r * (4 * Real.pi * (2 * r)))
            = ENNReal.ofReal (M * r) * ENNReal.ofReal (4 * Real.pi * (2 * r)) from
              ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_right h3 (ENNReal.ofReal (M * r))
      have harith : ENNReal.ofReal (M * (2 * Real.pi * (3 * r) ^ 2))
            + ENNReal.ofReal (M * (2 * Real.pi * (2 * r) ^ 2))
            + ENNReal.ofReal (M * r * (4 * Real.pi * (2 * r)))
          = ENNReal.ofReal (M * (34 * Real.pi * r ^ 2)) := by
        rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ M * (2 * Real.pi * (3 * r) ^ 2))
              (by positivity : (0:ℝ) ≤ M * (2 * Real.pi * (2 * r) ^ 2)),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      calc (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
            (M * ((‖(x + h) - y‖)⁻¹ + (‖x - y‖)⁻¹ + r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)))
          ≤ (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal (M * (‖(x + h) - y‖)⁻¹))
            + (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal (M * (‖x - y‖)⁻¹))
            + (∫⁻ y in Metric.closedBall (0 : R3) R ∩ small, ENNReal.ofReal
                (M * r * (‖x - y‖ ^ (2 : ℕ) : ℝ)⁻¹)) := hsplit
        _ ≤ ENNReal.ofReal (M * (2 * Real.pi * (3 * r) ^ 2))
            + ENNReal.ofReal (M * (2 * Real.pi * (2 * r) ^ 2))
            + ENNReal.ofReal (M * r * (4 * Real.pi * (2 * r))) :=
            add_le_add (add_le_add hB1 hB2) hB3
        _ = ENNReal.ofReal (M * (34 * Real.pi * r ^ 2)) := harith
    -- the far-region piece
    have hfar_bound : (∫⁻ y in Metric.closedBall (0 : R3) R ∩ far, ENNReal.ofReal
          (M * (10000 * r ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2))))
        ≤ ENNReal.ofReal (M * (80000 * Real.pi * Real.sqrt D * r ^ ((3 : ℝ) / 2))) := by
      have hsub : Metric.closedBall (0 : R3) R ∩ far ⊆ Metric.ball x D := by
        intro y hy
        obtain ⟨hyS, -⟩ := hy
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hyS
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev y x]
        have h1 : R ≤ |R| := le_abs_self R
        calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
          _ ≤ ‖x‖ + R := by linarith
          _ ≤ |R| + ‖x‖ := by linarith
          _ < |R| + ‖x‖ + 1 := by linarith
          _ = D := by rw [hDD]
      rw [show (fun y : R3 => ENNReal.ofReal (M * (10000 * r ^ ((3 : ℝ) / 2)
            * ‖x - y‖ ^ (-(5 : ℝ) / 2))))
          = fun y : R3 => ENNReal.ofReal (M * 10000 * r ^ ((3 : ℝ) / 2))
              * ENNReal.ofReal (‖x - y‖ ^ (-(5 : ℝ) / 2)) from by
            funext y
            rw [show M * (10000 * r ^ ((3 : ℝ) / 2) * ‖x - y‖ ^ (-(5 : ℝ) / 2))
                = (M * 10000 * r ^ ((3 : ℝ) / 2)) * (‖x - y‖ ^ (-(5 : ℝ) / 2)) by ring,
              ENNReal.ofReal_mul (by positivity)]]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have h3 : ∫⁻ y in Metric.ball x D, ENNReal.ofReal (‖x - y‖ ^ (-(5 : ℝ) / 2))
          ≤ ENNReal.ofReal (8 * Real.pi * Real.sqrt D) := by
        have hb := ball_lintegral_rpow_sub_le (s := -(5 : ℝ) / 2) (by norm_num) x hDpos
        refine hb.trans (le_of_eq ?_)
        rw [show -(5 : ℝ) / 2 + 3 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
        ring
      have hmono : (∫⁻ y in Metric.closedBall (0 : R3) R ∩ far,
            ENNReal.ofReal (‖x - y‖ ^ (-(5 : ℝ) / 2)))
          ≤ ENNReal.ofReal (8 * Real.pi * Real.sqrt D) :=
        (lintegral_mono_set hsub).trans h3
      refine (mul_le_mul_right hmono
        (ENNReal.ofReal (M * 10000 * r ^ ((3 : ℝ) / 2)))).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    have hsum : (∫⁻ y, ENNReal.ofReal ‖((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y‖)
        ≤ ENNReal.ofReal (M * (34 * Real.pi * r ^ 2
            + 80000 * Real.pi * Real.sqrt D * r ^ ((3 : ℝ) / 2))) := by
      refine hstep1.trans ?_
      have hR : ENNReal.ofReal (M * (34 * Real.pi * r ^ 2
            + 80000 * Real.pi * Real.sqrt D * r ^ ((3 : ℝ) / 2)))
          = ENNReal.ofReal (M * (34 * Real.pi * r ^ 2))
            + ENNReal.ofReal (M * (80000 * Real.pi * Real.sqrt D * r ^ ((3 : ℝ) / 2))) := by
        rw [show M * (34 * Real.pi * r ^ 2 + 80000 * Real.pi * Real.sqrt D * r ^ ((3 : ℝ) / 2))
            = M * (34 * Real.pi * r ^ 2)
              + M * (80000 * Real.pi * Real.sqrt D * r ^ ((3 : ℝ) / 2)) by ring,
          ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [hR]
      exact add_le_add hsmall_bound hfar_bound
    calc ‖∫ y, ((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y‖
        ≤ (∫⁻ y, ENNReal.ofReal ‖((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y‖).toReal :=
          norm_integral_le_lintegral_norm _
      _ ≤ (ENNReal.ofReal (M * (34 * Real.pi * r ^ 2
            + 80000 * Real.pi * Real.sqrt D * r ^ ((3 : ℝ) / 2)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
      _ = M * (34 * Real.pi * r ^ 2
            + 80000 * Real.pi * Real.sqrt D * r ^ ((3 : ℝ) / 2)) :=
          ENNReal.toReal_ofReal (by positivity)
      _ = M * (34 * Real.pi * ‖h‖ ^ 2
            + 80000 * Real.pi * Real.sqrt (|R| + ‖x‖ + 1) * ‖h‖ ^ ((3 : ℝ) / 2)) := by
          rw [hrr, hDD]

end

end Work.FTS.BSSwirl
