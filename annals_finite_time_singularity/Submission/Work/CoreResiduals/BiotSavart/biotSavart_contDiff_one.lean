import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_centered
import Submission.Work.CoreResiduals.BiotSavart.constant_vec_integral_ball_bsK_eq_zero
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_ball_integral
import Submission.Work.CoreResiduals.BiotSavart.continuous_bsDerivCLM
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology
open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-- **Reduction of the Hölder exponent.**  If `ω` is bounded by `M ≥ 0` and Hölder of exponent
`c > 0`, then it is Hölder with the (smaller) exponent `min c (1/2) < 1` and the (larger)
constant `max C (2M)`.  The estimates of the difference quotient need the exponent strictly
below `1`. -/
theorem holder_reduce {ω : R3 → R3} {M C c : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) :
    ∃ c' C' : ℝ, 0 < c' ∧ c' < 1 ∧ 0 ≤ C' ∧
      ∀ a b : R3, ‖ω a - ω b‖ ≤ C' * ‖a - b‖ ^ c' := by
  refine ⟨min c (1 / 2), max C (2 * M), lt_min hc (by norm_num),
    min_lt_of_right_lt (by norm_num), le_trans (by linarith : (0:ℝ) ≤ 2 * M) (le_max_right _ _),
    ?_⟩
  have hc' : (0:ℝ) < min c (1 / 2) := lt_min hc (by norm_num)
  have hC'nn : (0:ℝ) ≤ max C (2 * M) :=
    le_trans (by linarith : (0:ℝ) ≤ 2 * M) (le_max_right _ _)
  intro a b
  by_cases hab : a = b
  · subst hab
    rw [sub_self, norm_zero, sub_self, norm_zero]
    exact mul_nonneg hC'nn (Real.rpow_nonneg le_rfl _)
  have hx0 : (0:ℝ) < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have h1 : ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c := hhold a b
  by_cases hle : ‖a - b‖ ≤ 1
  · have hpow : ‖a - b‖ ^ c ≤ ‖a - b‖ ^ (min c (1 / 2)) := by
      have hsplit : ‖a - b‖ ^ c
          = ‖a - b‖ ^ (min c (1/2)) * ‖a - b‖ ^ (c - min c (1/2)) := by
        rw [← Real.rpow_add hx0, show min c (1/2) + (c - min c (1/2)) = c by ring]
      have hle1 : ‖a - b‖ ^ (c - min c (1/2)) ≤ 1 :=
        Real.rpow_le_one hx0.le hle (by linarith [min_le_left c (1/2)])
      rw [hsplit]
      nlinarith [Real.rpow_nonneg hx0.le (min c (1/2)), hle1]
    by_cases hC : 0 ≤ C
    · calc ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c := h1
        _ ≤ (max C (2 * M)) * ‖a - b‖ ^ c :=
            mul_le_mul_of_nonneg_right (le_max_left C (2 * M)) (Real.rpow_nonneg hx0.le c)
        _ ≤ (max C (2 * M)) * ‖a - b‖ ^ (min c (1 / 2)) :=
            mul_le_mul_of_nonneg_left hpow hC'nn
    · have hneg : C * ‖a - b‖ ^ c ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hC)) (Real.rpow_nonneg hx0.le c)
      calc ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c := h1
        _ ≤ 0 := hneg
        _ ≤ (max C (2 * M)) * ‖a - b‖ ^ (min c (1 / 2)) :=
            mul_nonneg hC'nn (Real.rpow_nonneg hx0.le _)
  · have hx1 : (1:ℝ) ≤ ‖a - b‖ := le_of_lt (not_le.mp hle)
    have h2M : ‖ω a - ω b‖ ≤ 2 * M := by
      calc ‖ω a - ω b‖ ≤ ‖ω a‖ + ‖ω b‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hbdd a) (hbdd b)
        _ = 2 * M := by ring
    have hone : (1:ℝ) ≤ ‖a - b‖ ^ (min c (1/2)) :=
      Real.one_le_rpow hx1 (le_min hc.le (by norm_num))
    calc ‖ω a - ω b‖ ≤ 2 * M := h2M
      _ ≤ (max C (2 * M)) * ‖a - b‖ ^ (min c (1 / 2)) := by
          have h3 : (2:ℝ) * M * 1 ≤ (2:ℝ) * M * ‖a - b‖ ^ (min c (1/2)) :=
            mul_le_mul_of_nonneg_left hone (by linarith)
          have h4 : (2:ℝ) * M ≤ max C (2 * M) := by
            rw [show (2:ℝ) * M = 2 * M from rfl]; exact le_max_right _ _
          nlinarith [h4, Real.rpow_nonneg (norm_nonneg (a - b)) (min c (1/2))]

/-- **Little-o relation** `‖h‖^{1+c} = o(‖h‖)` at `h = 0` for `c > 0`, the form in which the
difference-quotient bound feeds `HasFDerivAt`. -/
theorem isLittleO_norm_rpow {c : ℝ} (hc : 0 < c) :
    (fun h : R3 => ‖h‖ ^ (1 + c)) =o[𝓝 (0 : R3)] (fun h : R3 => h) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hεc : (0:ℝ) < ε ^ (1 / c) := Real.rpow_pos_of_pos hε _
  filter_upwards [Metric.ball_mem_nhds (0 : R3) hεc] with h hh
  have hnorm : ‖h‖ < ε ^ (1 / c) := by simpa [dist_eq_norm] using hh
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg h) _)]
  change ‖h‖ ^ (1 + c) ≤ ε * ‖h‖
  rcases eq_or_lt_of_le (norm_nonneg h) with h0 | h0
  · rw [← h0, Real.zero_rpow (by linarith : (1:ℝ) + c ≠ 0), mul_zero]
  · have hpow : ‖h‖ ^ c ≤ ε := by
      have h1 : ‖h‖ ^ c ≤ (ε ^ (1 / c)) ^ c := Real.rpow_le_rpow h0.le hnorm.le hc.le
      rwa [← Real.rpow_mul hε.le, one_div, inv_mul_cancel₀ (ne_of_gt hc), Real.rpow_one] at h1
    rw [Real.rpow_add h0, Real.rpow_one]
    nlinarith [hpow, h0]

/-- **`bsField ω ρ` is differentiable wherever the ball does not touch the support.**  The
difference-quotient bound `norm_bsField_diff_bound` gives an error of order `‖h‖^{1+c}`, and
`‖h‖^{1+c} = o(‖h‖)` (`isLittleO_norm_rpow`). -/
theorem hasFDerivAt_bsField {ω : R3 → R3} {R M C c : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hc : 0 < c)
    (hc1 : c < 1) (hC : 0 ≤ C) (hbdd : ∀ a, ‖ω a‖ ≤ M)
    (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    {ρ : ℝ} {x : R3} (hρ : R + ‖x‖ < ρ) :
    HasFDerivAt (bsField ω ρ) (bsDerivCLM ω ρ x) x := by
  obtain ⟨K, hK0, hK⟩ := norm_bsField_diff_bound hR hM hc hc1 hC hbdd hs hm hhold
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.trans_isLittleO ?_ (isLittleO_norm_rpow hc))
  refine Asymptotics.isBigO_iff.2 ⟨K, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : R3) (sub_pos.mpr hρ)] with h hh
  have hhρ : R + ‖x‖ + ‖h‖ < ρ := by
    have h2 : ‖h‖ < ρ - (R + ‖x‖) := by simpa [dist_eq_norm] using hh
    linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg h) _)]
  exact hK ρ x h hhρ

/-- **`C¹` of the Biot–Savart field (the Calderón–Zygmund chapter).**  For a vorticity `ω` that is
bounded, supported in `closedBall 0 R`, ae-strongly-measurable and Hölder of some positive exponent
`c` (the classical setting: `ω ∈ L^∞ ∩ C^{0,c}` compactly supported), the Newtonian-potential
Biot–Savart field is `C¹` on all of `ℝ³`.

The singularity at `x = y` is handled by the standard regularisation: since the kernel `bsK ω x a` is
odd about `a = x`, one may replace `ω` by `ω - ω x` and restrict the integral to the ball
`B(x, ρ)`, `ρ ≥ R + ‖x‖` (`biotSavart_centered`, `constant_vec_integral_ball_bsK_eq_zero`);
the resulting integrand is then dominated by `C‖x-a‖^{c-3}`, whose `a`-integral is finite and whose
`x`-derivative is dominated by `C'‖x-a‖^{c-3}`, integrable for `c > 0`.  Differentiating under the
integral sign then gives differentiability everywhere with a continuous derivative. -/
theorem biotSavart_contDiff_one {ω : Work.LWP.R3 → Work.LWP.R3} {R M C c : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) (hc : 0 < c) (hbdd : ∀ a, ‖ω a‖ ≤ M)
    (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) :
    ContDiff ℝ 1 (Work.LWP.biotSavart ω) := by
  obtain ⟨c', C', hc'0, hc'1, hC'0, hhold'⟩ := holder_reduce hc hM hbdd hhold
  rw [contDiff_iff_contDiffAt]
  intro x₀
  obtain ⟨K, hK0, hK⟩ := norm_bsField_diff_bound hR hM hc'0 hc'1 hC'0 hbdd hs hm hhold'
  set ρ : ℝ := R + ‖x₀‖ + 2 with hρdef
  have hρ' : R + ‖x₀‖ < ρ := by rw [hρdef]; linarith
  set U : Set R3 := Metric.ball x₀ 1 with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hx₀U : x₀ ∈ U := Metric.mem_ball_self one_pos
  have hUρ : ∀ x ∈ U, R + ‖x‖ < ρ := by
    intro x hx
    have h1 : ‖x - x₀‖ < 1 := by simpa [hU, dist_eq_norm] using hx
    have h2 : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
      have h := dist_triangle x x₀ 0
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at h
      linarith
    rw [hρdef]; linarith
  have hcont : ContinuousOn (fun x => (4 * Real.pi)⁻¹ • bsDerivCLM ω ρ x) U :=
    ((continuous_bsDerivCLM hc'0 hbdd hhold' ρ).continuousOn (s := U)).const_smul
      ((4 * Real.pi)⁻¹)
  have key : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1)
      (fun x => (4 * Real.pi)⁻¹ • bsField ω ρ x) U := by
    rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUopen.uniqueDiffOn]
    refine ⟨fun h => absurd h (by simp), fun x => (4 * Real.pi)⁻¹ • bsDerivCLM ω ρ x, ?_, ?_⟩
    · exact contDiffOn_zero.mpr hcont
    · intro x hx
      exact ((hasFDerivAt_bsField hR hM hc'0 hc'1 hC'0 hbdd hs hm hhold'
        (hUρ x hx)).const_smul ((4 * Real.pi)⁻¹)).hasFDerivWithinAt
  have hEq : ∀ x ∈ U, Work.LWP.biotSavart ω x = (4 * Real.pi)⁻¹ • bsField ω ρ x := by
    intro x hx
    exact biotSavart_ball_integral hM hbdd hs hm (le_of_lt (hUρ x hx))
  have hkey : ContDiffOn ℝ 1 (fun x => (4 * Real.pi)⁻¹ • bsField ω ρ x) U := by
    simpa using key
  exact (hkey.congr hEq).contDiffAt (Metric.ball_mem_nhds x₀ one_pos)

end Work.CoreResiduals.BiotSavart
