import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg
import Submission.Commons.NumberTheory.Zeta.psiBeta_nonneg_of_rh
import Submission.Commons.NumberTheory.Zeta.riemannZeta_ordinate_window
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal
import Submission.Commons.NumberTheory.Zeta.zeroSum_finset_le_beta
import Submission.Commons.NumberTheory.Zeta.divisor_xi_eq_logDeriv_pole_order
import Submission.Commons.Analysis.Real.integral_Ioi_chebyshevPsi_sub_id_mul_psiKfun_bound
import Submission.Commons.Analysis.Real.integrableOn_chebyshevPsi_sub_id_mul_psiKfun
import Submission.Commons.Analysis.Real.integral_psiKfun_le
import Submission.Commons.Analysis.Real.integral_rpow_neg_half_mul_psiKfun_le
import Submission.Commons.Analysis.Real.integral_mul_psiKfun_eq
import Submission.Commons.Analysis.Real.integral_mul_psiKfun_le_of_exp_one_le
import Submission.Commons.Analysis.Real.integral_log_mul_psiKfun_le_of_exp_one_le
import Submission.Commons.Analysis.Real.integral_mul_logsq_mul_psiKfun_le
import Submission.Commons.Analysis.Real.exists_gap_height
import Submission.Commons.Analysis.Real.exp_mul_le_of_le_div
import Submission.Commons.Analysis.Real.div_le_pow_of_le_div
import Submission.Commons.Analysis.Complex.integral_cpow_mul_psiKfun
import Submission.Commons.Analysis.Complex.integral_Fz_bound
import Submission.Commons.NumberTheory.Chebyshev.theta_integral_lower_bound

/-!
# The integrated lower bound for `∫_{Ioi x} (ψ(t) − t) k(t)`

Under RH, for every `ε > 0` there is `x₀` with
`∫_{Ioi x} (ψ(t) − t)·k(t) dt ≥ −(2β + ε)/(√x log x)` for all `x ≥ x₀`, where
`β = 2 + γ − log(4π)` and `k(t) = (log t + 1)/(t² (log t)²)`.

This is the integrated form of the truncated explicit formula for `ψ`
(`Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg`): integrating at a fixed good
height `T ≥ √Y (log Y)^{100}` with `Y = x (log x)^{100}`, the zero sum pulls out of the integral
and, under RH, `‖1 − ρ‖ = ‖ρ‖` together with `Σ_ρ m_ρ/‖ρ‖² ≤ β`
(`Commons.NumberTheory.Zeta.zeta1Order_sum_le_psiBeta`, inlined here to avoid an import cycle)
produces the leading constant `2β`.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators ComplexConjugate

noncomputable section
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Zeta

/-- The Route-B weight `k(t) = (log t + 1)/(t² (log t)²)`. -/
private noncomputable def psiKw (t : ℝ) : ℝ := (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)

/-- `β = 2 + γ − log(4π)` (the absolutely convergent zero sum `Σ_ρ 1/|ρ|²` under RH). -/
private noncomputable def psiBeta : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- The multiplicity-augmented `β`-sum for the zeros of `ζ₁`. -/
private theorem zeta1Order_sum_le_psiBeta (h : RiemannHypothesis) {R : ℝ} (hR : 0 ≤ R) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ ‖ρ‖ ≤ R ∧ (1 / 4 : ℝ) < ρ.re ∧ ρ.re < 2) :
    S.sum (fun ρ => (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) ≤ psiBeta := by
  have hb := zeroSum_finset_le_beta h R hR S hS
  refine le_trans (le_of_eq ?_) hb
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  obtain ⟨hζ, hρR, hre, hre2⟩ := hS ρ hρ
  have hspec := Classical.choose_spec (zeta1_logDeriv_pole_removal ρ hζ)
  have hζo : zeta1Order ρ = Classical.choose (zeta1_logDeriv_pole_removal ρ hζ) := by
    unfold zeta1Order
    rw [dif_pos hζ]
  have h1 : (zeta1Order ρ : ℤ) = (MeromorphicOn.divisor (fun z : ℂ =>
      (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
        (Metric.closedBall 0 R)) ρ := by
    rw [hζo]
    exact divisor_xi_eq_logDeriv_pole_order hR hζ hρR hre hre2 hspec.1 hspec.2
  have h2 : (zeta1Order ρ : ℝ) = (((MeromorphicOn.divisor (fun z : ℂ =>
      (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
        (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := by
    rw [← h1]; norm_num
  rw [h2]


lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  have h2pi : 2 * Real.pi ≤ 6.3 := by nlinarith [Real.pi_lt_d2]
  have h63 : Real.log 6.3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 6.3)]
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  exact le_trans (Real.log_le_log (by positivity) h2pi) h63

lemma complex_log_two_pi_norm_le_two : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ 2 := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcast : (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast]
  have hre : (Complex.log (((2 * Real.pi : ℝ)) : ℂ)).re = Real.log (2 * Real.pi) :=
    Complex.log_ofReal_re _
  have him : (Complex.log (((2 * Real.pi : ℝ)) : ℂ)).im = 0 := by
    rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hpos.le]
  have hval : Complex.log (((2 * Real.pi : ℝ)) : ℂ)
      = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hre]; simp
    · rw [him]; simp
  have hnorm : ‖((Real.log (2 * Real.pi) : ℝ) : ℂ)‖ = |Real.log (2 * Real.pi)| :=
    RCLike.norm_ofReal _
  rw [hval, hnorm]
  rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
  exact log_two_pi_le_two


private noncomputable def Gc (Z : Finset ℂ) (t : ℝ) : ℂ :=
  - Complex.log (2 * (Real.pi : ℂ)) - ∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (t : ℂ) ^ ρ / ρ

/-- `qX z = 1/(z^{1/2} log z)` (this form makes the numeric bookkeeping trivial). -/
private noncomputable def qX (z : ℝ) : ℝ := 1 / (z ^ (1 / 2 : ℝ) * Real.log z)

/-- `cfX z = 1 + (1 + 4/log z)/log z`. -/
private noncomputable def cfX (z : ℝ) : ℝ := 1 + (1 + 4 / Real.log z) / Real.log z

private theorem psiKw_continuousOn {x Y : ℝ} (hx2 : 2 ≤ x) (hxY : x ≤ Y) :
    ContinuousOn (fun t : ℝ => psiKw t) (Set.uIcc x Y) := by
  have hpos : ∀ t ∈ Set.uIcc x Y, (0 : ℝ) < t := by
    intro t ht
    rw [Set.uIcc_of_le hxY] at ht
    linarith [ht.1, hx2]
  have hlog : ∀ t ∈ Set.uIcc x Y, Real.log t ≠ 0 := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := by
      rw [Set.uIcc_of_le hxY] at ht; exact le_trans hx2 ht.1
    have h1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have h1 : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc x Y) :=
    Real.continuousOn_log.mono (fun t ht => by
      have hp := hpos t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hp)
  have hden : ContinuousOn (fun t : ℝ => t ^ 2 * (Real.log t) ^ 2) (Set.uIcc x Y) :=
    (continuousOn_id.pow 2).mul (h1.pow 2)
  have hne : ∀ t ∈ Set.uIcc x Y, t ^ 2 * (Real.log t) ^ 2 ≠ 0 := by
    intro t ht
    exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (hpos t ht))) (pow_ne_zero 2 (hlog t ht))
  have hmain : ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      (Set.uIcc x Y) := ContinuousOn.div (h1.add continuousOn_const) hden hne
  simpa [psiKw] using hmain

private theorem Gc_continuousOn {Z : Finset ℂ} {x Y : ℝ} (hxY : x ≤ Y)
    (hρ : ∀ ρ ∈ Z, (0 : ℝ) < ρ.re) :
    ContinuousOn (fun t : ℝ => Gc Z t) (Set.uIcc x Y) := by
  have hsum : ContinuousOn (fun t : ℝ => ∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (t : ℂ) ^ ρ / ρ)
      (Set.uIcc x Y) := by
    refine continuousOn_finsetSum Z ?_
    intro ρ hρmem
    have hc : Continuous (fun t : ℝ => (t : ℂ) ^ ρ) :=
      Complex.continuous_ofReal_cpow_const (hρ ρ hρmem)
    have hcc : ContinuousOn (fun _ : ℝ => ((zeta1Order ρ : ℂ) / ρ)) (Set.uIcc x Y) :=
      continuousOn_const
    have h := ContinuousOn.mul hcc hc.continuousOn
    rw [show ((fun _ : ℝ => ((zeta1Order ρ : ℂ) / ρ)) * (fun t : ℝ => (t : ℂ) ^ ρ))
        = (fun t : ℝ => (zeta1Order ρ : ℂ) * (t : ℂ) ^ ρ / ρ) from by
      funext t; simp only [Pi.mul_apply, div_eq_mul_inv]; ring] at h
    exact h
  exact ContinuousOn.sub continuousOn_const hsum

/-- **The zero-sum integral bound.**  Under RH the sum `∫_x^Y Gc·k` is bounded by
`2β(qX x·cfX x + qX Y·cfX Y)` plus the small `log 2π` term. -/
private theorem psi_zerosum_integral_bound (h : RiemannHypothesis)
    {Z : Finset ℂ} {x Y : ℝ}
    (hx2 : 2 ≤ x) (hxY : x ≤ Y)
    (hρ : ∀ ρ ∈ Z, ρ.re = (1 / 2 : ℝ))
    (hβ : ∑ ρ ∈ Z, (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2 ≤ psiBeta)
    (hIlog : ‖∫ t in x..Y, (psiKw t : ℂ)‖ ≤ 2 / (x * Real.log x))
    : ‖∫ t in x..Y, Gc Z t * (psiKw t : ℂ)‖
      ≤ ‖Complex.log (2 * (Real.pi : ℂ))‖ * (2 / (x * Real.log x))
        + psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y) := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hY1 : (1 : ℝ) < Y := lt_of_lt_of_le hx1 hxY
  have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hly : Real.log Y ≠ 0 := ne_of_gt (Real.log_pos hY1)
  have hρpos : ∀ ρ ∈ Z, (0 : ℝ) < ρ.re := by
    intro ρ hρmem; rw [hρ ρ hρmem]; norm_num
  have hkC : ContinuousOn (fun t : ℝ => (psiKw t : ℂ)) (Set.uIcc x Y) :=
    Complex.continuous_ofReal.comp_continuousOn (psiKw_continuousOn hx2 hxY)
  have hIpw : ∀ ρ ∈ Z, IntervalIntegrable
      (fun t : ℝ => ((zeta1Order ρ : ℂ) / ρ) * ((t : ℂ) ^ ρ * (psiKw t : ℂ))) volume x Y := by
    intro ρ hρmem
    have hc : Continuous (fun t : ℝ => (t : ℂ) ^ ρ) :=
      Complex.continuous_ofReal_cpow_const (hρpos ρ hρmem)
    exact (ContinuousOn.mul continuousOn_const
      (ContinuousOn.mul hc.continuousOn hkC)).intervalIntegrable
  have hIsum : IntervalIntegrable
      (fun t : ℝ => ∑ ρ ∈ Z, ((zeta1Order ρ : ℂ) / ρ) * ((t : ℂ) ^ ρ * (psiKw t : ℂ)))
      volume x Y := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finsetSum Z ?_
    intro ρ hρmem
    have hc : Continuous (fun t : ℝ => (t : ℂ) ^ ρ) :=
      Complex.continuous_ofReal_cpow_const (hρpos ρ hρmem)
    exact ContinuousOn.mul continuousOn_const (ContinuousOn.mul hc.continuousOn hkC)
  have hkCint : IntervalIntegrable (fun t : ℝ => (psiKw t : ℂ)) volume x Y := hkC.intervalIntegrable
  have hIconst : IntervalIntegrable
      (fun t : ℝ => (- Complex.log (2 * (Real.pi : ℂ))) * (psiKw t : ℂ)) volume x Y :=
    (ContinuousOn.mul continuousOn_const hkC).intervalIntegrable
  -- the algebraic decomposition
  have hdec : ∫ t in x..Y, Gc Z t * (psiKw t : ℂ)
      = -(Complex.log (2 * (Real.pi : ℂ))) * (∫ t in x..Y, (psiKw t : ℂ))
        - ∑ ρ ∈ Z, ((zeta1Order ρ : ℂ) / ρ)
            * (∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)) := by
    have hcongr : ∫ t in x..Y, Gc Z t * (psiKw t : ℂ)
        = ∫ t in x..Y, ((- Complex.log (2 * (Real.pi : ℂ))) * (psiKw t : ℂ)
            - ∑ ρ ∈ Z, ((zeta1Order ρ : ℂ) / ρ) * ((t : ℂ) ^ ρ * (psiKw t : ℂ))) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [Gc]
      rw [sub_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun ρ _ => by ring
    rw [hcongr, intervalIntegral.integral_sub hIconst hIsum,
      intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum (fun ρ hρmem => hIpw ρ hρmem)]
    congr 1
    exact Finset.sum_congr rfl fun ρ _ => by rw [intervalIntegral.integral_const_mul]
  -- the norm bound
  have hnorm : ‖∫ t in x..Y, Gc Z t * (psiKw t : ℂ)‖
      ≤ ‖Complex.log (2 * (Real.pi : ℂ))‖ * ‖∫ t in x..Y, (psiKw t : ℂ)‖
        + ∑ ρ ∈ Z, ((zeta1Order ρ : ℝ) / ‖ρ‖)
            * ‖∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)‖ := by
    rw [hdec]
    have hstep : ‖∑ ρ ∈ Z, ((zeta1Order ρ : ℂ) / ρ)
        * (∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ))‖
        ≤ ∑ ρ ∈ Z, ((zeta1Order ρ : ℝ) / ‖ρ‖)
            * ‖∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro ρ hρmem
      rw [norm_mul, norm_div, Complex.norm_natCast]
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add ?_ hstep
    rw [norm_mul, norm_neg]
  -- per-zero bound on `‖1 - ρ‖`
  have hnorm1 : ∀ ρ ∈ Z, ‖(1 : ℂ) - ρ‖ = ‖ρ‖ := by
    intro ρ hρmem
    have hsq : ‖(1 : ℂ) - ρ‖ ^ 2 = ‖ρ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      rw [hρ ρ hρmem]; ring
    nlinarith [hsq, norm_nonneg ((1 : ℂ) - ρ), norm_nonneg ρ]
  -- the `F_ρ` bound
  have hFρ : ∀ ρ ∈ Z, ‖∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)‖
      ≤ (2 / ‖ρ‖) * qX x * cfX x + (2 / ‖ρ‖) * qX Y * cfX Y := by
    intro ρ hρmem
    have h1 := Commons.Analysis.Complex.integral_cpow_mul_psiKfun (hρ ρ hρmem) hx2 hxY
    have hY2 : (2 : ℝ) ≤ Y := le_trans hx2 hxY
    have hbx := Commons.Analysis.Complex.integral_Fz_bound (z := ρ) (hρ ρ hρmem) hx2
    have hby := Commons.Analysis.Complex.integral_Fz_bound (z := ρ) (hρ ρ hρmem) hY2
    have hnx : ‖(1 : ℂ) - ρ‖ = ‖ρ‖ := hnorm1 ρ hρmem
    rw [hnx] at hbx hby
    have hcx : (2 / ‖ρ‖) * qX x * cfX x
        = 2 / ‖ρ‖ * x ^ (-(1 / 2) : ℝ) / Real.log x
          + 2 / ‖ρ‖ * x ^ (-(1 / 2) : ℝ) / (Real.log x) ^ 2 * (1 + 4 / Real.log x) := by
      simp only [qX, cfX]
      rw [Real.rpow_neg (le_of_lt hx0)]
      field_simp
    have hcy : (2 / ‖ρ‖) * qX Y * cfX Y
        = 2 / ‖ρ‖ * Y ^ (-(1 / 2) : ℝ) / Real.log Y
          + 2 / ‖ρ‖ * Y ^ (-(1 / 2) : ℝ) / (Real.log Y) ^ 2 * (1 + 4 / Real.log Y) := by
      simp only [qX, cfX]
      rw [Real.rpow_neg (le_of_lt (lt_of_lt_of_le hx0 hxY))]
      field_simp
    rw [← hcx] at hbx
    rw [← hcy] at hby
    have h2 : ‖∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)‖
        = ‖(∫ t in x..Y, (t : ℂ) ^ ρ
            * (((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) : ℝ) : ℂ))‖ := rfl
    rw [h2, h1]
    exact le_trans (norm_sub_le _ _) (add_le_add hbx hby)
  -- assemble
  have hstep : ∑ ρ ∈ Z, ((zeta1Order ρ : ℝ) / ‖ρ‖)
        * ‖∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)‖
      ≤ psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y) := by
    have h2 : ∑ ρ ∈ Z, ((zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
          * (2 * qX x * cfX x + 2 * qX Y * cfX Y)
        = (∑ ρ ∈ Z, (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
          * (2 * qX x * cfX x + 2 * qX Y * cfX Y) := (Finset.sum_mul ..).symm
    have h3 : ∑ ρ ∈ Z, ((zeta1Order ρ : ℝ) / ‖ρ‖)
          * ‖∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)‖
        ≤ ∑ ρ ∈ Z, ((zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
            * (2 * qX x * cfX x + 2 * qX Y * cfX Y) := by
      apply Finset.sum_le_sum
      intro ρ hρmem
      have h1 := hFρ ρ hρmem
      have h2' : (0 : ℝ) ≤ (zeta1Order ρ : ℝ) / ‖ρ‖ := by positivity
      have h3' : ((zeta1Order ρ : ℝ) / ‖ρ‖)
            * ((2 / ‖ρ‖) * qX x * cfX x + (2 / ‖ρ‖) * qX Y * cfX Y)
          = ((zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
            * (2 * qX x * cfX x + 2 * qX Y * cfX Y) := by
        field_simp
      calc ((zeta1Order ρ : ℝ) / ‖ρ‖) * ‖∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)‖
          ≤ ((zeta1Order ρ : ℝ) / ‖ρ‖)
            * ((2 / ‖ρ‖) * qX x * cfX x + (2 / ‖ρ‖) * qX Y * cfX Y) :=
            mul_le_mul_of_nonneg_left h1 h2'
        _ = _ := h3'
    refine le_trans h3 ?_
    rw [h2]
    exact mul_le_mul_of_nonneg_right hβ (by
      have hqx : 0 ≤ qX x := by
        simp only [qX]
        exact div_nonneg zero_le_one
          (mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.log_pos hx1)).le
      have hqy : 0 ≤ qX Y := by
        simp only [qX]
        exact div_nonneg zero_le_one
          (mul_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le hx0 hxY) _) (Real.log_pos hY1)).le
      have hcx : 0 ≤ cfX x := by
        have h : 0 ≤ (1 + 4 / Real.log x) / Real.log x :=
          div_nonneg (by
            have : 0 < 1 + 4 / Real.log x := by
              have := Real.log_pos hx1; positivity
            linarith) (le_of_lt (Real.log_pos hx1))
        simp only [cfX]; linarith
      have hcy : 0 ≤ cfX Y := by
        have h : 0 ≤ (1 + 4 / Real.log Y) / Real.log Y :=
          div_nonneg (by
            have : 0 < 1 + 4 / Real.log Y := by
              have := Real.log_pos hY1; positivity
            linarith) (le_of_lt (Real.log_pos hY1))
        simp only [cfX]; linarith
      nlinarith [hqx, hqy, hcx, hcy])
  -- final assembly
  refine le_trans hnorm ?_
  have h4 : ‖Complex.log (2 * (Real.pi : ℂ))‖ * ‖∫ t in x..Y, (psiKw t : ℂ)‖
        + ∑ ρ ∈ Z, ((zeta1Order ρ : ℝ) / ‖ρ‖)
            * ‖∫ t in x..Y, (t : ℂ) ^ ρ * (psiKw t : ℂ)‖
      ≤ ‖Complex.log (2 * (Real.pi : ℂ))‖ * (2 / (x * Real.log x))
        + psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y) :=
    add_le_add (mul_le_mul_of_nonneg_left hIlog (norm_nonneg _)) hstep
  exact h4

/-- **The error-term integral bound.**  If the pointwise error of the truncated explicit
formula is dominated by `C·K(L³/T)t + B`, then its `k`-weighted integral is dominated by
`C·K(L³/T)·2(loglog Y − loglog x) + B·2/(x log x)`. -/
private theorem psi_error_integral_bound {x Y T L C C₂ D K : ℝ} {Z : Finset ℂ}
    (hx1 : 1 < x) (hxe : Real.exp 1 ≤ x) (hxY : x ≤ Y)
    (hT1 : 1 ≤ T) (hL0 : 0 ≤ L) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hEr : ∀ t : ℝ, x ≤ t → t ≤ Y →
      ‖(((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Z t‖
        ≤ C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)))
    : ‖∫ t in x..Y, ((((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Z t) * (psiKw t : ℂ)‖
      ≤ C * K * (L ^ 3 / T) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
        + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) * (2 / (x * Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_of_lt Real.exp_one_gt_two) hxe
  have hknn : ∀ t : ℝ, x ≤ t → t ≤ Y → 0 ≤ psiKw t := by
    intro t hxt _
    have ht1 : 1 < t := lt_of_lt_of_le hx1 hxt
    have hl : 0 < Real.log t := Real.log_pos ht1
    simp only [psiKw]
    exact div_nonneg (by linarith) (by positivity)
  have hg : ∀ t : ℝ, x ≤ t → t ≤ Y →
      ‖((((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Z t) * (psiKw t : ℂ)‖
        ≤ (C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)))
          * psiKw t := by
    intro t hxt htY
    have hkt : ‖((psiKw t : ℝ) : ℂ)‖ = psiKw t := by
      rw [show ‖((psiKw t : ℝ) : ℂ)‖ = |psiKw t| from RCLike.norm_ofReal (psiKw t),
        abs_of_nonneg (hknn t hxt htY)]
    rw [norm_mul, hkt]
    exact mul_le_mul_of_nonneg_right (hEr t hxt htY) (hknn t hxt htY)
  have hbdd : IntervalIntegrable (fun t : ℝ =>
      (C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)))
        * psiKw t) volume x Y := by
    have hcont : ContinuousOn (fun t : ℝ =>
        (C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4))))
        (Set.uIcc x Y) := by fun_prop
    exact (ContinuousOn.mul hcont (psiKw_continuousOn hx2 hxY)).intervalIntegrable
  have hmain := intervalIntegral.norm_integral_le_of_norm_le hxY
    (Filter.Eventually.of_forall fun t ht => hg t (le_of_lt ht.1) ht.2) hbdd
  -- integrability of the two pieces
  have htk : IntervalIntegrable (fun t : ℝ => t * psiKw t) volume x Y := by
    have hcont : ContinuousOn (fun t : ℝ => t) (Set.uIcc x Y) := continuousOn_id
    exact (ContinuousOn.mul hcont (psiKw_continuousOn hx2 hxY)).intervalIntegrable
  have hk : IntervalIntegrable (fun t : ℝ => psiKw t) volume x Y :=
    (psiKw_continuousOn hx2 hxY).intervalIntegrable
  have hsplit : ∫ t in x..Y,
        (C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)))
          * psiKw t
      = C * K * (L ^ 3 / T) * (∫ t in x..Y, t * psiKw t)
        + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4))
          * (∫ t in x..Y, psiKw t) := by
    have hcongr : ∫ t in x..Y,
          (C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)))
            * psiKw t
        = ∫ t in x..Y, (C * K * (L ^ 3 / T) * (t * psiKw t)
            + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) * psiKw t) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [hcongr, intervalIntegral.integral_add (htk.const_mul _) (hk.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h1 : ∫ t in x..Y, t * psiKw t
      ≤ 2 * (Real.log (Real.log Y) - Real.log (Real.log x)) := by
    have hh := Commons.Analysis.Real.integral_mul_psiKfun_le_of_exp_one_le hxe hxY
    convert hh using 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [psiKw]
  have h2 : ∫ t in x..Y, psiKw t ≤ 2 / (x * Real.log x) := by
    have hh := Commons.Analysis.Real.integral_psiKfun_le hx1 hxY
    convert hh using 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [psiKw]
  refine le_trans hmain ?_
  rw [hsplit]
  refine add_le_add ?_ ?_
  · exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · exact mul_le_mul_of_nonneg_left h2 (by positivity)


/-- **The integrated explicit formula: final assembly.**  Tail bound + zero-sum bound +
error bound, with the numerical comparisons left as explicit hypotheses. -/
private theorem psi_integral_assembly (h : RiemannHypothesis)
    {Cp C C₂ D x Y T L K ε : ℝ} {Z : Finset ℂ}
    (hCp : 0 ≤ Cp) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hD : 0 ≤ D)
    (hx2 : 2 ≤ x) (hxe : Real.exp 1 ≤ x) (hxY : x ≤ Y)
    (hT1 : 1 ≤ T) (hK0 : 0 ≤ K) (hL0 : 0 ≤ L)
    (hε : 0 < ε) (hρ : ∀ ρ ∈ Z, ρ.re = (1 / 2 : ℝ))
    (hβ : ∑ ρ ∈ Z, (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2 ≤ psiBeta)
    (hE : ∀ t : ℝ, x ≤ t → t ≤ Y →
      ‖(((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Z t‖
        ≤ C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)))
    (hInt : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Chebyshev.psi t - t) * psiKw t) (Set.Ioi x))
    (hTail : ∀ Y' : ℝ, Y ≤ Y' → |∫ t in Set.Ioi Y', ((Chebyshev.psi t : ℝ) - t)
        * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))|
        ≤ Cp * (Real.log Y') ^ 9 / Y' ^ (1 / 2 : ℝ))
    (htailnum : Cp * (Real.log Y) ^ 9 / Y ^ (1 / 2 : ℝ)
        ≤ (ε / 2) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)))
    (hmainnum : ‖Complex.log (2 * (Real.pi : ℂ))‖ * (2 / (x * Real.log x))
        + psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y)
        + C * K * (L ^ 3 / T) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
        + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) * (2 / (x * Real.log x))
        ≤ (2 * psiBeta + ε / 2) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)))
    : -(2 * psiBeta + ε) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x))
      ≤ ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * psiKw t := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hY1 : (1 : ℝ) < Y := lt_of_lt_of_le hx1 hxY
  have hf : (fun t : ℝ => (Chebyshev.psi t - t) * psiKw t) = fun t => (Chebyshev.psi t - t) * psiKw t := rfl
  -- the tail
  have hIntY : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Chebyshev.psi t - t) * psiKw t) (Set.Ioi Y) :=
    hInt.mono_set (Set.Ioi_subset_Ioi hxY)
  have htailY : -(Cp * (Real.log Y) ^ 9 / Y ^ (1 / 2 : ℝ))
      ≤ ∫ t in Set.Ioi Y, (Chebyshev.psi t - t) * psiKw t := by
    have hh := hTail Y le_rfl
    have hfun : (fun t : ℝ => ((Chebyshev.psi t : ℝ) - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
        = (fun t : ℝ => (Chebyshev.psi t - t) * psiKw t) := by
      funext t; simp only [psiKw]
    rw [hfun] at hh
    exact (abs_le.mp hh).1
  -- the main integral
  have hIlog : ‖∫ t in x..Y, (psiKw t : ℂ)‖ ≤ 2 / (x * Real.log x) := by
    have hh : (∫ t in x..Y, ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
        ≤ 2 / (x * Real.log x) :=
      Commons.Analysis.Real.integral_psiKfun_le hx1 hxY
    have h1 : ‖∫ t in x..Y, (psiKw t : ℂ)‖ = |∫ t in x..Y, psiKw t| := by
      rw [intervalIntegral.integral_ofReal (f := fun t : ℝ => psiKw t)]
      exact RCLike.norm_ofReal _
    have h2 : |∫ t in x..Y, psiKw t| = ∫ t in x..Y, psiKw t := by
      rw [abs_of_nonneg]
      apply intervalIntegral.integral_nonneg hxY
      intro t ht
      have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hx1 ht.1
      have hl : 0 < Real.log t := Real.log_pos ht1
      simp only [psiKw]
      exact div_nonneg (by linarith) (by positivity)
    have h3 : ∫ t in x..Y, psiKw t ≤ 2 / (x * Real.log x) := by
      simpa only [psiKw] using hh
    rw [h1, h2]
    exact h3
  have hzerob := psi_zerosum_integral_bound h hx2 hxY hρ hβ hIlog
  have herrb := psi_error_integral_bound (Z := Z) hx1 hxe hxY hT1 hL0 hC hC₂ hD hK0 hE
  -- the split of `∫_x^Y`
  have hkC : ContinuousOn (fun t : ℝ => (psiKw t : ℂ)) (Set.uIcc x Y) :=
    Complex.continuous_ofReal.comp_continuousOn (psiKw_continuousOn hx2 hxY)
  have hGcC : ContinuousOn (fun t : ℝ => Gc Z t) (Set.uIcc x Y) :=
    Gc_continuousOn hxY (fun ρ hρmem => by rw [hρ ρ hρmem]; norm_num)
  have hIGc : IntervalIntegrable (fun t : ℝ => Gc Z t * (psiKw t : ℂ)) volume x Y :=
    (ContinuousOn.mul hGcC hkC).intervalIntegrable
  have hIFc : IntervalIntegrable
      (fun t : ℝ => (((Chebyshev.psi t - t : ℝ) : ℂ)) * (psiKw t : ℂ)) volume x Y := by
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Chebyshev.psi t - t) * psiKw t) (Set.Ioc x Y) :=
      hInt.mono_set Set.Ioc_subset_Ioi_self
    have h2 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (((Chebyshev.psi t - t) * psiKw t : ℝ) : ℂ)) (Set.Ioc x Y) :=
      MeasureTheory.Integrable.ofReal h1
    have h3 : IntervalIntegrable
        (fun t : ℝ => (((Chebyshev.psi t - t) * psiKw t : ℝ) : ℂ)) volume x Y :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hxY).mpr h2
    refine h3.congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Complex.ofReal_mul]
  have hIEr : IntervalIntegrable
      (fun t : ℝ => ((((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Z t) * (psiKw t : ℂ)) volume x Y := by
    have hsub := hIFc.sub hIGc
    refine hsub.congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  have hFc : ∫ t in x..Y, (((Chebyshev.psi t - t : ℝ) : ℂ)) * (psiKw t : ℂ)
      = (((∫ t in x..Y, (Chebyshev.psi t - t) * psiKw t) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal
      (f := fun t : ℝ => (Chebyshev.psi t - t) * psiKw t)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Complex.ofReal_mul]
  have hsplitc : ∫ t in x..Y, (((Chebyshev.psi t - t : ℝ) : ℂ)) * (psiKw t : ℂ)
      = (∫ t in x..Y, Gc Z t * (psiKw t : ℂ))
        + ∫ t in x..Y, ((((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Z t) * (psiKw t : ℂ) := by
    rw [← intervalIntegral.integral_add hIGc hIEr]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hmain : -(‖Complex.log (2 * (Real.pi : ℂ))‖ * (2 / (x * Real.log x))
        + psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y)
        + C * K * (L ^ 3 / T) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
        + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) * (2 / (x * Real.log x)))
      ≤ ∫ t in x..Y, (Chebyshev.psi t - t) * psiKw t := by
    have hre := congrArg Complex.re hFc
    simp only [Complex.ofReal_re] at hre
    rw [hsplitc] at hre
    rw [Complex.add_re] at hre
    have h1 : -(‖∫ t in x..Y, Gc Z t * (psiKw t : ℂ)‖)
        ≤ (∫ t in x..Y, Gc Z t * (psiKw t : ℂ)).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    have h2 : -(‖∫ t in x..Y, ((((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Z t) * (psiKw t : ℂ)‖)
        ≤ (∫ t in x..Y, ((((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Z t) * (psiKw t : ℂ)).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    rw [← hre]
    linarith [h1, h2, hzerob, herrb]
  -- combine
  rw [show ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * psiKw t
      = (∫ t in x..Y, (Chebyshev.psi t - t) * psiKw t)
        + ∫ t in Set.Ioi Y, (Chebyshev.psi t - t) * psiKw t from
    (integral_interval_add_Ioi hInt hIntY).symm]
  linarith [hmain, htailY, hmainnum, htailnum, hε]


/-- Numeric side condition (tail): `Cp·(log Y)^9/√Y ≤ (ε/2)·u`. -/
private theorem psi_assembly_tailnum {Cp x Y ε Sbig : ℝ}
    (hCp : 0 ≤ Cp) (hε : 0 < ε)
    (hx2 : 2 ≤ x) (hxY : x ≤ Y)
    (hLx100 : 100 ≤ Real.log x)
    (hYeq : Y = x * (Real.log x) ^ 100)
    (hlogYle : Real.log Y ≤ 101 * Real.log x)
    (hThr : ∀ v : ℝ, 0 ≤ v → v ≤ Sbig → v / ε ≤ Real.log x)
    (hSbigCp : 2.2 * 10 ^ 18 * Cp ≤ Sbig)
    : Cp * (Real.log Y) ^ 9 / Y ^ (1 / 2 : ℝ)
      ≤ (ε / 2) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hLx0 : 0 < Real.log x := by linarith
  have hLx1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le hx0 hxY
  have hLY1 : (1 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log hx0 hxY; linarith
  have hYsqrt : Y ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50 := by
    rw [← Real.sqrt_eq_rpow, hYeq, Real.sqrt_mul (le_of_lt hx0),
      show (Real.log x) ^ 100 = ((Real.log x) ^ 50) ^ 2 by ring,
      Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow]
  have hden : 0 < x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50 :=
    mul_pos (Real.rpow_pos_of_pos hx0 _) (pow_pos hLx0 50)
  have hLY9 : (Real.log Y) ^ 9 ≤ (101 * Real.log x) ^ 9 :=
    pow_le_pow_left₀ (le_of_lt (Real.log_pos (lt_of_lt_of_le hx1 hxY))) hlogYle 9
  have hstep1 : Cp * (Real.log Y) ^ 9 / Y ^ (1 / 2 : ℝ)
      ≤ Cp * (101 * Real.log x) ^ 9 / (x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50) := by
    rw [hYsqrt]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLY9 hCp) hden.le
  have hstep2 : Cp * (101 * Real.log x) ^ 9 / (x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50)
      = (Cp * 101 ^ 9 / (Real.log x) ^ 40) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) := by
    rw [mul_pow]
    rw [show (50 : ℕ) = 41 + 9 by norm_num, pow_add]
    rw [show (41 : ℕ) = 40 + 1 by norm_num, pow_add]
    field_simp
  have hfinal : Cp * 101 ^ 9 / (Real.log x) ^ 40 ≤ ε / 2 := by
    rcases eq_or_lt_of_le hCp with hCp0 | hCp0
    · rw [← hCp0]; simp only [zero_mul, zero_div]
      exact div_nonneg hε.le (by norm_num)
    · have hthrCp : 2.2 * 10 ^ 18 * Cp / ε ≤ Real.log x := hThr _ (by positivity) hSbigCp
      have hLx40 : 2.2 * 10 ^ 18 * Cp / ε ≤ (Real.log x) ^ 40 := by
        have h1 : Real.log x ≤ (Real.log x) ^ 40 := by
          simpa using pow_le_pow_right₀ hLx1 (by norm_num : (1 : ℕ) ≤ 40)
        linarith
      have hb : 0 < 2.2 * 10 ^ 18 * Cp / ε := by positivity
      have h101 : (101 : ℝ) ^ 9 ≤ 1.1 * 10 ^ 18 := by norm_num
      have hle1 : Cp * 101 ^ 9 / (Real.log x) ^ 40
          ≤ Cp * 101 ^ 9 / (2.2 * 10 ^ 18 * Cp / ε) :=
        div_le_div_of_nonneg_left (by positivity) hb hLx40
      have hle2 : Cp * 101 ^ 9 / (2.2 * 10 ^ 18 * Cp / ε) = 101 ^ 9 * ε / (2.2 * 10 ^ 18) := by
        field_simp
      have hle3 : (101 : ℝ) ^ 9 * ε / (2.2 * 10 ^ 18) ≤ ε / 2 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2.2 * 10 ^ 18)]
        nlinarith [h101, hε.le]
      calc Cp * 101 ^ 9 / (Real.log x) ^ 40
          ≤ Cp * 101 ^ 9 / (2.2 * 10 ^ 18 * Cp / ε) := hle1
        _ = 101 ^ 9 * ε / (2.2 * 10 ^ 18) := hle2
        _ ≤ ε / 2 := hle3
  calc Cp * (Real.log Y) ^ 9 / Y ^ (1 / 2 : ℝ)
      ≤ Cp * (101 * Real.log x) ^ 9 / (x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50) := hstep1
    _ = (Cp * 101 ^ 9 / (Real.log x) ^ 40) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) := hstep2
    _ ≤ (ε / 2) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) :=
        mul_le_mul_of_nonneg_right hfinal
          (le_of_lt (one_div_pos.mpr (mul_pos (Real.rpow_pos_of_pos hx0 _) hLx0)))

/-- The four numerical identities/bounds reducing `mainnum` to pure arithmetic. -/
private theorem psi_assembly_numfacts {x Y : ℝ} (hx2 : 2 ≤ x) (hxY : x ≤ Y)
    (hLx100 : 100 ≤ Real.log x)
    (hYeq : Y = x * (Real.log x) ^ 100)
    (hLY1 : (1 : ℝ) ≤ Real.log Y) :
    (qX x = 1 / (x ^ (1 / 2 : ℝ) * Real.log x))
    ∧ (qX Y ≤ (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) / (Real.log x) ^ 49)
    ∧ (cfX x ≤ 1 + 2 / Real.log x) ∧ (cfX Y ≤ 3) := by
  have hx0 : 0 < x := by linarith
  have hLx0 : 0 < Real.log x := by linarith
  have hLx4 : (4 : ℝ) ≤ Real.log x := by linarith
  have hLx1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le hx0 hxY
  have hLY0 : 0 < Real.log Y := lt_of_lt_of_le zero_lt_one hLY1
  have hYhalf : Y ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50 := by
    rw [← Real.sqrt_eq_rpow, hYeq, Real.sqrt_mul (le_of_lt hx0),
      show (Real.log x) ^ 100 = ((Real.log x) ^ 50) ^ 2 by ring,
      Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow]
  have hLY4 : (4 : ℝ) ≤ Real.log Y := by
    rw [hYeq, Real.log_mul (ne_of_gt hx0) (pow_ne_zero 100 (ne_of_gt hLx0)), Real.log_pow]
    have h0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hLx1
    push_cast; linarith
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have hu : (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) / (Real.log x) ^ 49
        = 1 / (x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50) := by
      field_simp
    rw [hu, show qX Y = 1 / (Y ^ (1 / 2 : ℝ) * Real.log Y) from rfl, hYhalf]
    apply one_div_le_one_div_of_le
    · positivity
    · have : x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50 * Real.log Y
          = (x ^ (1 / 2 : ℝ) * (Real.log x) ^ 50) * Real.log Y := rfl
      rw [this]
      exact le_mul_of_one_le_right (by positivity) hLY1
  · have h4 : 4 / Real.log x ≤ 1 := by rw [div_le_iff₀ hLx0]; linarith
    have hmain : (1 + 4 / Real.log x) / Real.log x ≤ 2 / Real.log x :=
      div_le_div_of_nonneg_right (by linarith) hLx0.le
    simp only [cfX]
    linarith
  · have h4 : 4 / Real.log Y ≤ 4 := by rw [div_le_iff₀ hLY0]; linarith
    have h5 : (5 : ℝ) ≤ 2 * Real.log Y := by linarith
    have hmain : (1 + 4 / Real.log Y) / Real.log Y ≤ 2 := by
      rw [div_le_iff₀ hLY0]; linarith
    simp only [cfX]
    linarith

/-- **The main numerical side condition of Route B.**  Every term of the pointwise-error
integral bound is `≤ (ε/12)·u` except the `2β·u` leading term, whose correction is also
`≤ (ε/12)·u`; hence the total is `≤ (2β + 5ε/12)·u ≤ (2β + ε/2)·u`.
All hypotheses are threshold statements about `log x`, `x^{1/2}`, `x²` and `T`. -/
private theorem psi_assembly_mainnum {C C₂ D x Y T L K ε : ℝ}
    (hx2 : 2 ≤ x) (hxY : x ≤ Y)
    (hT1 : 1 ≤ T) (hL0 : 0 ≤ L) (hK0 : 0 ≤ K) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hD : 0 ≤ D)
    (hε : 0 < ε)
    (hβ0 : 0 ≤ psiBeta) (hlog2pi : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ 2)
    (hLx100 : 100 ≤ Real.log x)
    (hLle : L ≤ 20000 * Real.log x)
    (hYeq : Y = x * (Real.log x) ^ 100)
    (hTbig : Real.sqrt Y * (Real.log Y) ^ 100 ≤ T)
    (hlogYle : Real.log Y ≤ 101 * Real.log x)
    (hllY : Real.log (Real.log Y) ≤ 101 * Real.log x)
    (hβ48 : 48 * psiBeta / ε ≤ Real.log x)
    (hβ72 : 72 * psiBeta / ε ≤ Real.log x)
    (hLxbig : 2 * 10 ^ 16 * (C * K) / ε ≤ Real.log x)
    (hX1 : 48 / ε ≤ x ^ (1 / 2 : ℝ))
    (hX2 : 288 * L / ε ≤ x ^ (1 / 2 : ℝ))
    (hX3 : 144 * C₂ * L / ε ≤ x ^ (1 / 2 : ℝ))
    (hX4 : 144 * D * L ^ 4 / ε ≤ x ^ 2)
    : ‖Complex.log (2 * (Real.pi : ℂ))‖ * (2 / (x * Real.log x))
      + psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y)
      + C * K * (L ^ 3 / T) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
      + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) * (2 / (x * Real.log x))
      ≤ (2 * psiBeta + ε / 2) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hLx0 : 0 < Real.log x := by linarith
  have hLx1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hT0 : 0 < T := by linarith
  have hxhalf : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hYpos : 0 < Y := lt_of_lt_of_le hx0 hxY
  have hLY1 : (1 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log hx0 hxY; linarith
  have hLY0 : 0 < Real.log Y := lt_of_lt_of_le zero_lt_one hLY1
  have hLYx : Real.log x ≤ Real.log Y := Real.log_le_log hx0 hxY
  have hxy : (x ^ (1 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ)) = x := by
    rw [← Real.sqrt_eq_rpow]; exact Real.mul_self_sqrt hx0.le
  obtain ⟨hqx, hqY, hcfx, hcfY⟩ := psi_assembly_numfacts hx2 hxY hLx100 hYeq hLY1
  set u : ℝ := 1 / (x ^ (1 / 2 : ℝ) * Real.log x) with hu
  have hu0 : 0 < u := by rw [hu]; exact div_pos one_pos (mul_pos hxhalf hLx0)
  have hqxu : qX x = u := hqx.trans hu.symm
  -- positivity of the building blocks
  have hqx0 : 0 ≤ qX x := by rw [hqxu]; exact hu0.le
  have hqxY0 : 0 ≤ qX Y := by
    simp only [qX]
    exact div_nonneg zero_le_one
      (mul_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le hx0 hxY) _) hLY0).le
  have hcfx0 : 0 ≤ cfX x := by
    have h : 0 ≤ (1 + 4 / Real.log x) / Real.log x :=
      div_nonneg (by have h4 : 0 ≤ 4 / Real.log x := div_nonneg (by norm_num) hLx0.le; linarith)
        hLx0.le
    simp only [cfX]; linarith
  have hcfY0 : 0 ≤ cfX Y := by
    have h : 0 ≤ (1 + 4 / Real.log Y) / Real.log Y :=
      div_nonneg (by have h4 : 0 ≤ 4 / Real.log Y := div_nonneg (by norm_num) hLY0.le; linarith)
        hLY0.le
    simp only [cfX]; linarith
  -- the denominators
  have hA1 : 2 / (x * Real.log x) = (2 / x ^ (1 / 2 : ℝ)) * u := by
    have h1 : x * Real.log x = (x ^ (1 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ)) * Real.log x := by
      rw [hxy]
    rw [h1, hu]
    field_simp
  -- (T1) the `log 2π` term
  have hT1b : ‖Complex.log (2 * (Real.pi : ℂ))‖ * (2 / (x * Real.log x)) ≤ (ε / 12) * u := by
    rw [hA1]
    have h2 : ‖Complex.log (2 * (Real.pi : ℂ))‖ * ((2 / x ^ (1 / 2 : ℝ)) * u)
        = (2 * ‖Complex.log (2 * (Real.pi : ℂ))‖ / x ^ (1 / 2 : ℝ)) * u := by ring
    rw [h2]
    refine mul_le_mul_of_nonneg_right ?_ hu0.le
    have h4 : 2 * ‖Complex.log (2 * (Real.pi : ℂ))‖ / x ^ (1 / 2 : ℝ) ≤ 4 / x ^ (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_right (by linarith [hlog2pi]) hxhalf.le
    have h5 : 4 / x ^ (1 / 2 : ℝ) ≤ 4 / (48 / ε) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hX1
    have h6 : 4 / (48 / ε) = ε / 12 := by field_simp; ring
    linarith [h4, h5, h6]
  -- (T2) the zero-sum term
  have hT2b : psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y)
      ≤ (2 * psiBeta + ε / 12 + ε / 12) * u := by
    have h1 : qX x * cfX x ≤ u * (1 + 2 / Real.log x) := by
      rw [hqxu]
      exact mul_le_mul_of_nonneg_left hcfx hu0.le
    have h2 : qX Y * cfX Y ≤ (u / (Real.log x) ^ 49) * 3 := by
      refine mul_le_mul hqY hcfY hcfY0 ?_
      exact div_nonneg hu0.le (pow_pos hLx0 49).le
    have hβ48' : 48 * psiBeta ≤ Real.log x * ε := by
      have h := hβ48; rw [div_le_iff₀ hε] at h; linarith
    have hb48 : 4 * psiBeta / Real.log x ≤ ε / 12 := by
      rw [div_le_iff₀ hLx0]; linarith
    have hβ72' : 72 * psiBeta ≤ Real.log x * ε := by
      have h := hβ72; rw [div_le_iff₀ hε] at h; linarith
    have hLx49 : Real.log x ≤ (Real.log x) ^ 49 := by
      simpa using pow_le_pow_right₀ hLx1 (by norm_num : (1 : ℕ) ≤ 49)
    have hb72 : 6 * psiBeta / (Real.log x) ^ 49 ≤ ε / 12 := by
      rw [div_le_iff₀ (pow_pos hLx0 49)]
      nlinarith [hβ72', hLx49, hε.le]
    have e1 : 2 * (qX x * cfX x) ≤ 2 * (u * (1 + 2 / Real.log x)) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have e2 : 2 * (qX Y * cfX Y) ≤ 2 * ((u / (Real.log x) ^ 49) * 3) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    rw [show psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y)
        = psiBeta * (2 * (qX x * cfX x)) + psiBeta * (2 * (qX Y * cfX Y)) by ring]
    have f1 : psiBeta * (2 * (qX x * cfX x)) ≤ psiBeta * (2 * (u * (1 + 2 / Real.log x))) :=
      mul_le_mul_of_nonneg_left e1 hβ0
    have f2 : psiBeta * (2 * (qX Y * cfX Y)) ≤ psiBeta * (2 * ((u / (Real.log x) ^ 49) * 3)) :=
      mul_le_mul_of_nonneg_left e2 hβ0
    have g1 : psiBeta * (2 * (u * (1 + 2 / Real.log x)))
        = 2 * psiBeta * u + u * (4 * psiBeta / Real.log x) := by
      field_simp; ring
    have g2 : psiBeta * (2 * ((u / (Real.log x) ^ 49) * 3))
        = u * (6 * psiBeta / (Real.log x) ^ 49) := by
      field_simp; ring
    have g3 : u * (4 * psiBeta / Real.log x) ≤ u * (ε / 12) :=
      mul_le_mul_of_nonneg_left hb48 hu0.le
    have g4 : u * (6 * psiBeta / (Real.log x) ^ 49) ≤ u * (ε / 12) :=
      mul_le_mul_of_nonneg_left hb72 hu0.le
    linarith [f1, f2, g1, g2, g3, g4]
  -- shared facts for (T3) and (T4)
  have hYsqrt : Real.sqrt Y = Real.sqrt x * (Real.log x) ^ 50 := by
    rw [hYeq, Real.sqrt_mul hx0.le,
      show (Real.log x) ^ 100 = ((Real.log x) ^ 50) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hTge : Real.sqrt x * (Real.log x) ^ 50 * (Real.log Y) ^ 100 ≤ T := by
    have h := hTbig; rw [hYsqrt] at h; exact h
  have hTmin0 : 0 < Real.sqrt x * (Real.log x) ^ 50 * (Real.log Y) ^ 100 := by
    have h1 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have h2 : 0 < (Real.log x) ^ 50 := pow_pos hLx0 50
    have h3 : 0 < (Real.log Y) ^ 100 := pow_pos hLY0 100
    positivity
  have hxhalf_eq : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  have hsqrtne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
  have hLxne : Real.log x ≠ 0 := ne_of_gt hLx0
  have hLYne : Real.log Y ≠ 0 := ne_of_gt hLY0
  have hx32 : x ^ (-(3 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ) = 1 / x ^ 2 := by
    rw [← Real.rpow_add hx0, show (-(3 / 2) : ℝ) + (-(1 / 2)) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hx0.le (2 : ℝ)]
    simp [one_div, Real.rpow_natCast]
  -- (T3) the Perron truncation term
  have hT3b : C * K * (L ^ 3 / T) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
      ≤ (ε / 12) * u := by
    have hll0 : Real.log (Real.log x) ≤ Real.log (Real.log Y) :=
      Real.log_le_log hLx0 hLYx
    have hllx0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hLx1
    have hd : 2 * (Real.log (Real.log Y) - Real.log (Real.log x)) ≤ 202 * Real.log x := by
      linarith [hllY, hll0, hllx0]
    have hd0 : 0 ≤ 2 * (Real.log (Real.log Y) - Real.log (Real.log x)) := by linarith
    have hCK0 : 0 ≤ C * K := mul_nonneg hC hK0
    have hLx30 : 0 ≤ (Real.log x) ^ 3 := pow_nonneg hLx0.le 3
    have hL3 : L ^ 3 ≤ 8 * 10 ^ 12 * (Real.log x) ^ 3 := by
      have h1 : L ^ 3 ≤ (20000 * Real.log x) ^ 3 := pow_le_pow_left₀ hL0 hLle 3
      have h2 : (20000 * Real.log x) ^ 3 = 8 * 10 ^ 12 * (Real.log x) ^ 3 := by ring
      rw [h2] at h1; exact h1
    have hQ0 : 0 ≤ C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3) * (202 * Real.log x)
        * (x ^ (1 / 2 : ℝ) * Real.log x) := by
      have h1 : 0 ≤ 8 * 10 ^ 12 * (Real.log x) ^ 3 := mul_nonneg (by norm_num) hLx30
      exact mul_nonneg (mul_nonneg (mul_nonneg hCK0 h1) (by linarith [hLx0]))
        (mul_pos hxhalf hLx0).le
    have hnum : C * K * (L ^ 3) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
          * (x ^ (1 / 2 : ℝ) * Real.log x)
        ≤ C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3) * (202 * Real.log x)
          * (x ^ (1 / 2 : ℝ) * Real.log x) := by
      have s1 : C * K * (L ^ 3) ≤ C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3) :=
        mul_le_mul_of_nonneg_left hL3 hCK0
      have s2 : (C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3))
            * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
          ≤ (C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3)) * (202 * Real.log x) := by
        apply mul_le_mul_of_nonneg_left hd
        exact mul_nonneg hCK0 (mul_nonneg (by norm_num) hLx30)
      have s3 : (C * K * (L ^ 3)) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
          ≤ (C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3))
            * (2 * (Real.log (Real.log Y) - Real.log (Real.log x))) :=
        mul_le_mul_of_nonneg_right s1 hd0
      calc C * K * (L ^ 3) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
            * (x ^ (1 / 2 : ℝ) * Real.log x)
          = ((C * K * (L ^ 3)) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x))))
            * (x ^ (1 / 2 : ℝ) * Real.log x) := by ring
        _ ≤ ((C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3))
              * (2 * (Real.log (Real.log Y) - Real.log (Real.log x))))
            * (x ^ (1 / 2 : ℝ) * Real.log x) :=
            mul_le_mul_of_nonneg_right s3 (mul_pos hxhalf hLx0).le
        _ ≤ ((C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3)) * (202 * Real.log x))
            * (x ^ (1 / 2 : ℝ) * Real.log x) :=
            mul_le_mul_of_nonneg_right s2 (mul_pos hxhalf hLx0).le
        _ = C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3) * (202 * Real.log x)
            * (x ^ (1 / 2 : ℝ) * Real.log x) := by ring
    have hdT : C * K * (L ^ 3) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
          * (x ^ (1 / 2 : ℝ) * Real.log x) / T
        = C * K * (L ^ 3 / T) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
          * (x ^ (1 / 2 : ℝ) * Real.log x) := by
      field_simp
    rw [hu, mul_one_div, le_div_iff₀ (mul_pos hxhalf hLx0), ← hdT]
    calc C * K * (L ^ 3) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
          * (x ^ (1 / 2 : ℝ) * Real.log x) / T
        ≤ C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3) * (202 * Real.log x)
            * (x ^ (1 / 2 : ℝ) * Real.log x) / T :=
          div_le_div_of_nonneg_right hnum hT0.le
      _ ≤ C * K * (8 * 10 ^ 12 * (Real.log x) ^ 3) * (202 * Real.log x)
            * (x ^ (1 / 2 : ℝ) * Real.log x)
            / (Real.sqrt x * (Real.log x) ^ 50 * (Real.log Y) ^ 100) :=
          div_le_div_of_nonneg_left hQ0 hTmin0 hTge
      _ = 1616 * 10 ^ 12 * (C * K) / ((Real.log x) ^ 45 * (Real.log Y) ^ 100) := by
          rw [hxhalf_eq]; field_simp; ring
      _ ≤ ε / 12 := by
          have h := hLxbig
          rw [div_le_iff₀ hε] at h
          have hLx45 : Real.log x ≤ (Real.log x) ^ 45 := by
            simpa using pow_le_pow_right₀ hLx1 (by norm_num : (1 : ℕ) ≤ 45)
          have h1 : (1 : ℝ) ≤ (Real.log Y) ^ 100 := one_le_pow₀ hLY1
          have h2 : (0:ℝ) < (Real.log x) ^ 45 := pow_pos hLx0 45
          have h3 : (0:ℝ) < (Real.log x) ^ 45 * (Real.log Y) ^ 100 :=
            mul_pos h2 (pow_pos hLY0 100)
          have h4 : Real.log x ≤ (Real.log x) ^ 45 * (Real.log Y) ^ 100 := by
            have h5 := mul_le_mul hLx45 h1 (by norm_num : (0 : ℝ) ≤ 1) (pow_nonneg hLx0.le 45)
            simpa using h5
          have h6 : Real.log x * ε ≤ (Real.log x) ^ 45 * (Real.log Y) ^ 100 * ε :=
            mul_le_mul_of_nonneg_right h4 hε.le
          rw [div_le_iff₀ h3]
          nlinarith [h, h6, hCK0, hε.le]
  -- (T4) the remaining error term
  have hT4b : (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) * (2 / (x * Real.log x))
      ≤ (ε / 12) * u := by
    rw [hA1]
    have hfac : (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) * (2 / x ^ (1 / 2 : ℝ))
        = 4 * C₂ * L * (x ^ (-(1 / 2) : ℝ)) + 8 * L * (x ^ (-(1 / 2) : ℝ))
          + 2 * D * L ^ 4 * (x ^ (-(3 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ)) := by
      rw [show (2 / x ^ (1 / 2 : ℝ)) = 2 * x ^ (-(1 / 2) : ℝ) from by
        rw [Real.rpow_neg hx0.le (1 / 2)]; ring]
      ring
    have hexp : (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4))
          * ((2 / x ^ (1 / 2 : ℝ)) * u)
        = (4 * C₂ * L * (x ^ (-(1 / 2) : ℝ)) + 8 * L * (x ^ (-(1 / 2) : ℝ))
          + 2 * D * L ^ 4 * (x ^ (-(3 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ))) * u := by
      rw [← mul_assoc, hfac]
    rw [hexp]
    refine mul_le_mul_of_nonneg_right ?_ hu0.le
    rw [hx32]
    have ha : 4 * C₂ * L * (x ^ (-(1 / 2) : ℝ)) ≤ ε / 36 := by
      rw [Real.rpow_neg hx0.le (1 / 2), inv_eq_one_div,
        show 4 * C₂ * L * (1 / x ^ (1 / 2 : ℝ)) = 4 * C₂ * L / x ^ (1 / 2 : ℝ) by ring,
        div_le_iff₀ hxhalf]
      have h := hX3
      rw [div_le_iff₀ hε] at h
      linarith
    have hb : 8 * L * (x ^ (-(1 / 2) : ℝ)) ≤ ε / 36 := by
      rw [Real.rpow_neg hx0.le (1 / 2), inv_eq_one_div,
        show 8 * L * (1 / x ^ (1 / 2 : ℝ)) = 8 * L / x ^ (1 / 2 : ℝ) by ring,
        div_le_iff₀ hxhalf]
      have h := hX2
      rw [div_le_iff₀ hε] at h
      linarith
    have hc : 2 * D * L ^ 4 * (1 / x ^ 2) ≤ ε / 36 := by
      rw [show 2 * D * L ^ 4 * (1 / x ^ 2) = 2 * D * L ^ 4 / x ^ 2 by ring,
        div_le_iff₀ (pow_pos hx0 2)]
      have h := hX4
      rw [div_le_iff₀ hε] at h
      have hx20 : 0 ≤ ε * x ^ 2 := mul_nonneg hε.le (sq_nonneg x)
      linarith [h, hx20]
    linarith [ha, hb, hc]
  -- assemble
  have h12 : (5 : ℝ) / 12 ≤ 1 / 2 := by norm_num
  have htot : (2 * psiBeta + ε / 12 + ε / 12) * u + (ε / 12) * u + (ε / 12) * u + (ε / 12) * u
      ≤ (2 * psiBeta + ε / 2) * u := by
    nlinarith [hu0.le, hε.le, h12]
  linarith [hT1b, hT2b, hT3b, hT4b, htot]



/-- `x^{1/2} = exp(log x / 2)`. -/
private lemma rpow_half_eq_exp (x : ℝ) (hx : 0 < x) :
    x ^ (1 / 2 : ℝ) = Real.exp (Real.log x / 2) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1; ring

/-- `exp (2 log x) = x^2`. -/
private lemma exp_two_log_eq_sq (x : ℝ) (hx : 0 < x) :
    Real.exp (2 * Real.log x) = x ^ 2 := by
  rw [show (2 : ℝ) * Real.log x = ((2 : ℕ) : ℝ) * Real.log x by norm_num,
    Real.exp_nat_mul, Real.exp_log hx]

/-- `t^{-3/2} ≤ x^{-3/2}` for `0 < x ≤ t`. -/
private lemma rpow_neg_three_halves_le {x t : ℝ} (hx : 0 < x) (hxt : x ≤ t) :
    t ^ (-(3 / 2) : ℝ) ≤ x ^ (-(3 / 2) : ℝ) := by
  have h1 : x ^ (3 / 2 : ℝ) ≤ t ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hx.le hxt (by norm_num)
  have h4 : t ^ (-(3 / 2) : ℝ) = 1 / t ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_neg (le_trans hx.le hxt) (3 / 2), one_div]
  have h5 : x ^ (-(3 / 2) : ℝ) = 1 / x ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_neg hx.le (3 / 2), one_div]
  rw [h4, h5]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx _) h1

/-- `48/ε ≤ x^{1/2}` from `2304/ε² ≤ x`. -/
private lemma le_rpow_half_of_le_div_sq {x ε : ℝ} (hε : 0 < ε) (h : 2304 / ε ^ 2 ≤ x) :
    48 / ε ≤ x ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  have h1 : Real.sqrt (2304 / ε ^ 2) = 48 / ε := by
    have h2 : Real.sqrt (ε ^ 2) = ε := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hε]
    have h3 : Real.sqrt (2304 : ℝ) = 48 := by
      rw [show (2304 : ℝ) = 48 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2304), h2, h3]
  rw [← h1]
  exact Real.sqrt_le_sqrt h

/-- `10^40(S₁+1)^3 + 1` dominates `c·X` when `X ≤ S₁` and `c ≤ 10^40`. -/
private lemma sbig_ge_mul_of_le {Sbig S₁ X c : ℝ}
    (hSbig : Sbig = 10 ^ 40 * (S₁ + 1) ^ 3 + 1)
    (hX0 : 0 ≤ X) (hXS : X ≤ S₁) (hS₁0 : 0 ≤ S₁) (hc : 0 ≤ c) (hc' : c ≤ 10 ^ 40) :
    c * X ≤ Sbig := by
  have h1 : (1 : ℝ) ≤ S₁ + 1 := by linarith
  have h2 : S₁ ≤ (S₁ + 1) ^ 3 := by
    have h := pow_le_pow_right₀ h1 (show (1 : ℕ) ≤ 3 by norm_num)
    calc S₁ ≤ S₁ + 1 := by linarith
      _ = (S₁ + 1) ^ 1 := (pow_one _).symm
      _ ≤ (S₁ + 1) ^ 3 := h
  have h3 : c * X ≤ 10 ^ 40 * S₁ := by
    calc c * X ≤ 10 ^ 40 * X := mul_le_mul_of_nonneg_right hc' hX0
      _ ≤ 10 ^ 40 * S₁ := mul_le_mul_of_nonneg_left hXS (by norm_num)
  have h4 : (10 : ℝ) ^ 40 * S₁ ≤ 10 ^ 40 * (S₁ + 1) ^ 3 :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  rw [hSbig]; linarith

/-- `10^40(S₁+1)^3 + 1` dominates `c·X` when `X ≤ 6(S₁+1)^2` and `c ≤ 10^36`. -/
private lemma sbig_ge_mul_of_sq_le {Sbig S₁ X c : ℝ}
    (hSbig : Sbig = 10 ^ 40 * (S₁ + 1) ^ 3 + 1)
    (hX0 : 0 ≤ X) (hXS : X ≤ 6 * (S₁ + 1) ^ 2) (hS₁0 : 0 ≤ S₁) (hc : 0 ≤ c)
    (hc' : c ≤ 10 ^ 36) :
    c * X ≤ Sbig := by
  have h1 : (1 : ℝ) ≤ S₁ + 1 := by linarith
  have h3 : c * X ≤ 10 ^ 36 * (6 * (S₁ + 1) ^ 2) := by
    calc c * X ≤ 10 ^ 36 * X := mul_le_mul_of_nonneg_right hc' hX0
      _ ≤ 10 ^ 36 * (6 * (S₁ + 1) ^ 2) := mul_le_mul_of_nonneg_left hXS (by norm_num)
  have h4 : (10 : ℝ) ^ 36 * (6 * (S₁ + 1) ^ 2) ≤ 10 ^ 40 * (S₁ + 1) ^ 3 := by
    have h5 : (6 * 10 ^ 36 : ℝ) ≤ 10 ^ 40 * (S₁ + 1) := by nlinarith
    calc (10 : ℝ) ^ 36 * (6 * (S₁ + 1) ^ 2) = (6 * 10 ^ 36) * (S₁ + 1) ^ 2 := by ring
      _ ≤ (10 ^ 40 * (S₁ + 1)) * (S₁ + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = 10 ^ 40 * (S₁ + 1) ^ 3 := by ring
  rw [hSbig]; linarith


/-- The pointwise error of the truncated explicit formula is dominated by
`C·K(L³/T)t + 2C₂L + 4L + D·x^{-3/2}L⁴`. -/
private lemma ef_le_dominated {C C₂ D K L T x t : ℝ} (hC₂0 : 0 ≤ C₂) (hD0 : 0 ≤ D)
    (hL0 : 0 ≤ L) (h32 : t ^ (-(3 / 2) : ℝ) ≤ x ^ (-(3 / 2) : ℝ)) :
    C * (t * L ^ 3 / T) * K
      + C₂ * (L * (min 1 (2 * t / (T * |t - (Nat.floor t : ℝ)|))
          + min 1 (2 * t / (T * |t - ((Nat.floor t : ℝ) + 1)|))))
      + (if (Nat.floor t : ℝ) = t then 4 * L else 0)
      + D * (t ^ (-(3 / 2) : ℝ) * L ^ 4)
    ≤ C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) := by
  have hm : min 1 (2 * t / (T * |t - (Nat.floor t : ℝ)|))
      + min 1 (2 * t / (T * |t - ((Nat.floor t : ℝ) + 1)|)) ≤ 2 := by
    have ha := min_le_left (1 : ℝ) (2 * t / (T * |t - (Nat.floor t : ℝ)|))
    have hb := min_le_left (1 : ℝ) (2 * t / (T * |t - ((Nat.floor t : ℝ) + 1)|))
    linarith
  have hL4 : (0 : ℝ) ≤ L ^ 4 := pow_nonneg hL0 4
  have hif : (if (Nat.floor t : ℝ) = t then 4 * L else 0) ≤ 4 * L := by
    split_ifs with hh
    · exact le_rfl
    · linarith
  have e1 : C * (t * L ^ 3 / T) * K = C * K * (L ^ 3 / T) * t := by ring
  have e2 : C₂ * (L * (min 1 (2 * t / (T * |t - (Nat.floor t : ℝ)|))
        + min 1 (2 * t / (T * |t - ((Nat.floor t : ℝ) + 1)|)))) ≤ 2 * C₂ * L := by
    have h3 : L * (min 1 (2 * t / (T * |t - (Nat.floor t : ℝ)|))
        + min 1 (2 * t / (T * |t - ((Nat.floor t : ℝ) + 1)|))) ≤ 2 * L := by
      nlinarith only [hm, hL0]
    exact le_trans (mul_le_mul_of_nonneg_left h3 hC₂0) (le_of_eq (by ring))
  have e4 : D * (t ^ (-(3 / 2) : ℝ) * L ^ 4) ≤ D * (x ^ (-(3 / 2) : ℝ) * L ^ 4) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h32 hL4) hD0
  linarith only [e1, e2, e4, hif]

/-- `288L/ε ≤ exp (Lx/2)`. -/
private lemma exp_half_ge_L {Sbig L Lx ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h200 : 200 ≤ Sbig) (hL0 : 0 ≤ L) (hLx : L ≤ 20000 * Lx)
    (hH : (Sbig / 2) / ε ≤ Lx / 2) :
    288 * L / ε ≤ Real.exp (Lx / 2) := by
  have hv : (1 : ℝ) ≤ Sbig / 2 := by linarith
  have hvw : 3628800 * (11520000 : ℝ) ≤ (Sbig / 2) ^ 9 := by
    have h1 : (100 : ℝ) ≤ Sbig / 2 := by linarith
    have h4 : (100 : ℝ) ^ 9 ≤ (Sbig / 2) ^ 9 := pow_le_pow_left₀ (by norm_num) h1 9
    have h5 : 3628800 * (11520000 : ℝ) ≤ 100 ^ 9 := by norm_num
    linarith only [h5, h4]
  have hmain := Commons.Analysis.Real.exp_mul_le_of_le_div (v := Sbig / 2) (w := 11520000)
    hε hε1 hv (by norm_num) hvw hH
  have hle : 288 * L / ε ≤ 11520000 * (Lx / 2) / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    have h3 : (11520000 : ℝ) * (Lx / 2) = 5760000 * Lx := by ring
    rw [h3]
    nlinarith only [hLx, hL0]
  linarith only [hmain, hle]

/-- `144C₂L/ε ≤ exp (Lx/2)`. -/
private lemma exp_half_ge_C2L {Sbig C₂ L Lx ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h200 : 200 ≤ Sbig) (hC₂0 : 0 ≤ C₂) (hC₂ : 10 ^ 14 * C₂ ≤ Sbig) (hL0 : 0 ≤ L)
    (hLx : L ≤ 20000 * Lx) (hH : (Sbig / 2) / ε ≤ Lx / 2) :
    144 * C₂ * L / ε ≤ Real.exp (Lx / 2) := by
  have hv : (1 : ℝ) ≤ Sbig / 2 := by linarith
  have hvw : 3628800 * (5760000 * C₂) ≤ (Sbig / 2) ^ 9 := by
    have h1 : (1 : ℝ) ≤ Sbig / 2 := by linarith
    have h2 : Sbig / 2 ≤ (Sbig / 2) ^ 9 := by
      simpa using pow_le_pow_right₀ h1 (by norm_num : (1 : ℕ) ≤ 9)
    have h3 : 3628800 * (5760000 * C₂) ≤ 21 * 10 ^ 12 * C₂ := by nlinarith only [hC₂0]
    have h4 : 21 * 10 ^ 12 * C₂ ≤ Sbig / 2 := by nlinarith only [hC₂, hC₂0]
    linarith only [h3, h4, h2]
  have hmain := Commons.Analysis.Real.exp_mul_le_of_le_div (v := Sbig / 2) (w := 5760000 * C₂)
    hε hε1 hv (by positivity) hvw hH
  have hle : 144 * C₂ * L / ε ≤ 5760000 * C₂ * (Lx / 2) / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    have h3 : (5760000 : ℝ) * C₂ * (Lx / 2) = 2880000 * C₂ * Lx := by ring
    rw [h3]
    nlinarith only [hLx, hL0, hC₂0]
  linarith only [hmain, hle]

/-- `144D·L⁴/ε ≤ exp (2Lx)`. -/
private lemma exp_two_log_ge_DL4 {Sbig D L Lx ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h200 : 200 ≤ Sbig) (hD0 : 0 ≤ D) (hD : 10 ^ 39 * D ≤ Sbig) (hL0 : 0 ≤ L)
    (hLx : L ≤ 20000 * Lx) (hLx0 : 0 ≤ Lx) (hH : (Sbig / 2) / ε ≤ Lx) :
    144 * D * L ^ 4 / ε ≤ Real.exp (2 * Lx) := by
  have hv : (1 : ℝ) ≤ Sbig / 2 := by linarith
  have hvw : (2304 * 10 ^ 16 : ℝ) * 2432902008176640000 * D ≤ (Sbig / 2) ^ 16 := by
    have h1 : (1 : ℝ) ≤ Sbig / 2 := by linarith
    have h2 : Sbig / 2 ≤ (Sbig / 2) ^ 16 := by
      simpa using pow_le_pow_right₀ h1 (by norm_num : (1 : ℕ) ≤ 16)
    have h4 : (2304 * 10 ^ 16 : ℝ) * 2432902008176640000 * D ≤ Sbig / 2 := by
      nlinarith only [hD, hD0]
    linarith only [h4, h2]
  have hlog16 : (2304 * 10 ^ 16 : ℝ) * 2432902008176640000 * D / ε ≤ Lx ^ 16 :=
    Commons.Analysis.Real.div_le_pow_of_le_div (v := Sbig / 2) (m := 16)
      hε hε1 hv (by norm_num) (by positivity) hvw hH
  have hlog16' : (2304 * 10 ^ 16 : ℝ) * 2432902008176640000 * D ≤ Lx ^ 16 * ε := by
    have h := hlog16
    rw [div_le_iff₀ hε] at h
    linarith only [h]
  have hmul : (2304 * 10 ^ 16 : ℝ) * 2432902008176640000 * D * Lx ^ 4 ≤ Lx ^ 20 * ε := by
    have h := mul_le_mul_of_nonneg_right hlog16' (pow_nonneg hLx0 4)
    have e : Lx ^ 16 * ε * Lx ^ 4 = Lx ^ 20 * ε := by ring
    linarith only [h, e]
  have hA : 144 * D * L ^ 4 / ε ≤ 2304 * 10 ^ 16 * D * Lx ^ 4 / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    have h1 : L ^ 4 ≤ (20000 * Lx) ^ 4 := pow_le_pow_left₀ hL0 hLx 4
    have h2 : (20000 * Lx) ^ 4 = 16 * 10 ^ 16 * Lx ^ 4 := by ring
    rw [h2] at h1
    nlinarith only [h1, hD0]
  have hB : 2304 * 10 ^ 16 * D * Lx ^ 4 / ε
      ≤ (2 ^ 20 / (Nat.factorial 20 : ℝ)) * Lx ^ 20 := by
    have hf : (Nat.factorial 20 : ℝ) = 2432902008176640000 := by norm_num
    rw [hf, div_le_iff₀ hε]
    have h2 : (2 ^ 20 / 2432902008176640000 : ℝ) * Lx ^ 20 * ε
        = (2 ^ 20 * (Lx ^ 20 * ε)) / 2432902008176640000 := by ring
    rw [h2, le_div_iff₀ (by norm_num : (0:ℝ) < 2432902008176640000)]
    have h6 : (0 : ℝ) ≤ Lx ^ 20 * ε := mul_nonneg (pow_nonneg hLx0 20) hε.le
    have h7 : Lx ^ 20 * ε ≤ 2 ^ 20 * (Lx ^ 20 * ε) := by
      have h8 : (1 : ℝ) ≤ 2 ^ 20 := by norm_num
      nlinarith only [h6, h8]
    have hmul' : (2304 * 10 ^ 16 : ℝ) * D * Lx ^ 4 * 2432902008176640000 ≤ Lx ^ 20 * ε := by
      have e : (2304 * 10 ^ 16 : ℝ) * D * Lx ^ 4 * 2432902008176640000
          = (2304 * 10 ^ 16 : ℝ) * 2432902008176640000 * D * Lx ^ 4 := by ring
      rw [e]; exact hmul
    linarith only [hmul', h7]
  have hexp : (2 ^ 20 / (Nat.factorial 20 : ℝ)) * Lx ^ 20 ≤ Real.exp (2 * Lx) := by
    have h1 : (2 * Lx) ^ 20 / (Nat.factorial 20 : ℝ) ≤ Real.exp (2 * Lx) :=
      Real.pow_div_factorial_le_exp (2 * Lx) (by linarith) 20
    have h2 : (2 * Lx) ^ 20 = 2 ^ 20 * Lx ^ 20 := by rw [mul_pow]
    rw [h2] at h1
    linarith only [h1]
  linarith only [hA, hB, hexp]


/-- The main integrated lower bound for `∫_{Ioi x}(ψ − t)k`. -/

theorem psi_integral_lower_bound (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → -(2 * (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) + ε) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) ≤ ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  show ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → -(2 * psiBeta + ε) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) ≤ ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * psiKw t
  obtain ⟨C, C₂, D, hC, hC₂, hD, x₁, hform⟩ := chebyshevPsi_at_height_farLeft_neg h
  obtain ⟨Cp, hCp, Yt, htail⟩ :=
    Commons.Analysis.Real.integral_Ioi_chebyshevPsi_sub_id_mul_psiKfun_bound h
  obtain ⟨c₀, hc₀, hwin⟩ := riemannZeta_ordinate_window h
  obtain ⟨xi0, hxi0⟩ := Commons.Analysis.Real.integrableOn_chebyshevPsi_sub_id_mul_psiKfun h
  have hβ0 : 0 ≤ psiBeta := by simpa only [psiBeta] using psiBeta_nonneg_of_rh h
  set S₁ : ℝ := C + C₂ + D + Cp + c₀ + psiBeta + 1 with hS₁
  have hS₁0 : 0 ≤ S₁ := by rw [hS₁]; linarith [hC.le, hC₂.le, hD.le, hCp.le, hc₀.le, hβ0]
  have hS₁1 : 1 ≤ S₁ := by rw [hS₁]; linarith [hC.le, hC₂.le, hD.le, hCp.le, hc₀.le, hβ0]
  have hC_le : C ≤ S₁ := by rw [hS₁]; linarith [hC₂.le, hD.le, hCp.le, hc₀.le, hβ0]
  have hC₂_le : C₂ ≤ S₁ := by rw [hS₁]; linarith [hC.le, hD.le, hCp.le, hc₀.le, hβ0]
  have hD_le : D ≤ S₁ := by rw [hS₁]; linarith [hC.le, hC₂.le, hCp.le, hc₀.le, hβ0]
  have hCp_le : Cp ≤ S₁ := by rw [hS₁]; linarith [hC.le, hC₂.le, hD.le, hc₀.le, hβ0]
  have hc₀_le : c₀ ≤ S₁ := by rw [hS₁]; linarith [hC.le, hC₂.le, hD.le, hCp.le, hβ0]
  have hβ_le : psiBeta ≤ S₁ := by rw [hS₁]; linarith [hC.le, hC₂.le, hD.le, hCp.le, hc₀.le]
  set Sbig : ℝ := 10 ^ 40 * (S₁ + 1) ^ 3 + 1 with hSbig
  have hSbig0 : (0:ℝ) ≤ Sbig := by
    rw [hSbig]
    have h : (0:ℝ) ≤ 10^40 * (S₁ + 1)^3 :=
      mul_nonneg (by norm_num) (pow_nonneg (by linarith only [hS₁0]) 3)
    linarith only [h]
  set B : ℝ := 100 + Sbig / ε with hB
  have hB100 : (100 : ℝ) ≤ B := by
    rw [hB]; exact le_add_of_nonneg_right (div_nonneg hSbig0 hε.le)
  have hBge : Sbig / ε ≤ B := by rw [hB]; linarith
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      -(2 * psiBeta + ε) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) ≤
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * psiKw t := by
    filter_upwards [Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop B),
      Filter.eventually_ge_atTop (max (max (max x₁ 2) Yt) (max xi0 (2304 / ε ^ 2)))] with x hlog hx
    have hLx100 : (100 : ℝ) ≤ Real.log x := le_trans hB100 hlog
    have hLx1 : (1 : ℝ) ≤ Real.log x := by linarith only [hLx100]
    have hLx0 : 0 < Real.log x := by linarith only [hLx100]
    have hx2 : (2 : ℝ) ≤ x :=
      le_trans (le_trans (le_trans (le_max_right x₁ 2) (le_max_left _ _)) (le_max_left _ _)) hx
    have hx1 : (1 : ℝ) < x := by linarith only [hx2]
    have hxpos : 0 < x := by linarith only [hx2]
    have hxe : Real.exp 1 ≤ x := by
      calc Real.exp 1 ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hLx1
        _ = x := Real.exp_log hxpos
    have hxx1 : x₁ ≤ x :=
      le_trans (le_trans (le_trans (le_max_left x₁ 2) (le_max_left _ _)) (le_max_left _ _)) hx
    have hxYt : Yt ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hxxi0 : xi0 ≤ x := le_trans (le_trans (le_max_left xi0 _) (le_max_right _ _)) hx
    have hxbig : 2304 / ε ^ 2 ≤ x := le_trans (le_trans (le_max_right xi0 _) (le_max_right _ _)) hx
    -- ## thresholds `v/ε ≤ log x` for `v ≤ Sbig`
    have hthr : ∀ v : ℝ, 0 ≤ v → v ≤ Sbig → v / ε ≤ Real.log x := by
      intro v _ hv
      have h1 : v / ε ≤ Sbig / ε := div_le_div_of_nonneg_right hv hε.le
      linarith only [h1, hBge, hlog]
    have hSbig1 : (1 : ℝ) ≤ Sbig := by
      rw [hSbig]
      have hh : (0:ℝ) ≤ 10 ^ 40 * (S₁ + 1) ^ 3 :=
        mul_nonneg (by norm_num) (pow_nonneg (by linarith only [hS₁0]) 3)
      linarith only [hh]
    have hcube : S₁ + 1 ≤ (S₁ + 1) ^ 3 := by
      have h1 : (1 : ℝ) ≤ S₁ + 1 := by linarith only [hS₁0]
      simpa using pow_le_pow_right₀ h1 (show (1 : ℕ) ≤ 3 by norm_num)
    have hS₁le : S₁ ≤ Sbig := by
      rw [hSbig]
      calc S₁ ≤ S₁ + 1 := le_add_of_nonneg_right zero_le_one
        _ ≤ (S₁ + 1) ^ 3 := hcube
        _ = 1 * (S₁ + 1) ^ 3 := (one_mul _).symm
        _ ≤ 10 ^ 40 * (S₁ + 1) ^ 3 :=
            mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ) ≤ 10^40) (pow_nonneg (by linarith only [hS₁0]) 3)
        _ ≤ 10 ^ 40 * (S₁ + 1) ^ 3 + 1 := le_add_of_nonneg_right zero_le_one
    -- ## Y and the good height
    set Y : ℝ := x * (Real.log x) ^ 100 with hY
    have hxY : x ≤ Y := by
      rw [hY]
      have h1 : (1 : ℝ) ≤ (Real.log x) ^ 100 := one_le_pow₀ hLx1
      calc x = x * 1 := by ring
        _ ≤ x * (Real.log x) ^ 100 := mul_le_mul_of_nonneg_left h1 hxpos.le
    have hYpos : 0 < Y := lt_of_lt_of_le hxpos hxY
    have hlogY : Real.log Y = Real.log x + 100 * Real.log (Real.log x) := by
      rw [hY, Real.log_mul (ne_of_gt hxpos) (pow_ne_zero 100 (ne_of_gt hLx0)), Real.log_pow]
      push_cast; ring
    have hll_le : Real.log (Real.log x) ≤ Real.log x := by
      have h := Real.log_le_sub_one_of_pos hLx0
      linarith only [h]
    have hlogYle : Real.log Y ≤ 101 * Real.log x := by rw [hlogY]; linarith only [hll_le]
    have hlogYge : (1 : ℝ) ≤ Real.log Y := by
      have h1 := Real.log_le_log hxpos hxY
      linarith only [h1, hLx1]
    set T₀ : ℝ := Real.sqrt Y * (Real.log Y) ^ 100 with hT₀
    have hT₀5 : (5 : ℝ) ≤ T₀ := by
      rw [hT₀]
      have h1 : (1 : ℝ) ≤ Real.sqrt Y := Real.one_le_sqrt.mpr (le_trans (by norm_num : (1:ℝ) ≤ 2) (le_trans hx2 hxY))
      have hlogY100 : (100 : ℝ) ≤ Real.log Y := by
        have h0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg (by linarith only [hLx1])
        rw [hlogY]; linarith only [h0, hLx100]
      have h2 : (5 : ℝ) ≤ (Real.log Y) ^ 100 := by
        have hL1' : (1 : ℝ) ≤ Real.log Y := by linarith only [hlogY100]
        have h3 : Real.log Y ≤ (Real.log Y) ^ 100 := by
          simpa using pow_le_pow_right₀ hL1' (by norm_num : (1 : ℕ) ≤ 100)
        exact le_trans (by linarith only [hlogY100] : (5:ℝ) ≤ Real.log Y) h3
      calc (5 : ℝ) = 5 * 1 := by ring
        _ ≤ (Real.log Y) ^ 100 * Real.sqrt Y :=
            mul_le_mul h2 h1 (by norm_num) (pow_nonneg (by linarith only [hlogY100]) 100)
        _ = Real.sqrt Y * (Real.log Y) ^ 100 := by ring
    obtain ⟨Sw, hSwin, hScard, hSword⟩ := hwin T₀ hT₀5
    set n : ℕ := Sw.card + 1 with hn
    have hn1 : 1 ≤ n := by omega
    have hcardn : Sw.card ≤ n := by omega
    obtain ⟨T, hTlo, hThi, hTgap⟩ :=
      Commons.Analysis.Real.exists_gap_height T₀ hn1 Sw hcardn hSwin
    have hT5 : (5 : ℝ) ≤ T := le_trans hT₀5 hTlo
    have hT0 : 0 < T := by linarith only [hT5]
    have hsY : Real.sqrt Y ≤ T := by
      have h1 : Real.sqrt Y ≤ T₀ := by
        rw [hT₀]
        have h2 : (1 : ℝ) ≤ (Real.log Y) ^ 100 := one_le_pow₀ hlogYge
        calc Real.sqrt Y = Real.sqrt Y * 1 := by ring
          _ ≤ Real.sqrt Y * (Real.log Y) ^ 100 :=
              mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg Y)
      exact le_trans h1 hTlo
    have hsqY : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt (le_of_lt hYpos)
    have hT2Y : Y ≤ T ^ 2 := by
      have h3 : (Real.sqrt Y) ^ 2 ≤ T ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg Y) hsY 2
      rw [hsqY] at h3
      have h4 := h3
      clear hsY hsqY
      exact h4
    set δ : ℝ := 1 / (2 * (n : ℝ) + 2) with hδ
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h2n : (0:ℝ) < 2 * (n:ℝ) + 2 := by linarith only [hn0]
    have hδ0 : 0 < δ := by rw [hδ]; exact div_pos one_pos h2n
    have hδle : δ ≤ 1 := by
      rw [hδ, div_le_one h2n]
      linarith only [hn0]
    set K : ℝ := 2 * c₀ + 4 with hK
    have hK1 : (1 : ℝ) ≤ K := by rw [hK]; linarith only [hc₀.le]
    have hK_le : K ≤ 2 * S₁ + 4 := by rw [hK]; linarith only [hc₀_le]
    have hCK_le : C * K ≤ Sbig := by
      have hK0 : 0 ≤ K := by linarith only [hK1]
      have h1 : C * K ≤ S₁ * (2 * S₁ + 4) := by
        calc C * K ≤ S₁ * K := mul_le_mul_of_nonneg_right hC_le hK0
          _ ≤ S₁ * (2 * S₁ + 4) := mul_le_mul_of_nonneg_left hK_le hS₁0
      have h2 : S₁ * (2 * S₁ + 4) ≤ 4 * (S₁ + 1) ^ 2 := by
        clear hsY hsqY hT2Y hT0
        nlinarith only [hS₁0]
      have h3 : 4 * (S₁ + 1) ^ 2 ≤ 10 ^ 40 * (S₁ + 1) ^ 3 := by
        have h4 : (0:ℝ) ≤ (S₁ + 1) ^ 2 := pow_nonneg (by linarith only [hS₁0]) 2
        have h5 : (4:ℝ) ≤ 10 ^ 40 * (S₁ + 1) := by
          have h6 : (1:ℝ) ≤ S₁ + 1 := by linarith only [hS₁0]
          calc (4:ℝ) ≤ 10 ^ 40 := by norm_num
            _ = 10 ^ 40 * 1 := (mul_one _).symm
            _ ≤ 10 ^ 40 * (S₁ + 1) := mul_le_mul_of_nonneg_left h6 (by norm_num)
        calc 4 * (S₁ + 1) ^ 2 ≤ (10 ^ 40 * (S₁ + 1)) * (S₁ + 1) ^ 2 :=
              mul_le_mul_of_nonneg_right h5 h4
          _ = 10 ^ 40 * (S₁ + 1) ^ 3 := by ring
      rw [hSbig]
      linarith only [h1, h2, h3]
    have hC₂_le_big : C₂ ≤ Sbig := le_trans hC₂_le hS₁le
    have hD_le_big : D ≤ Sbig := le_trans hD_le hS₁le
    have hCp_le_big : Cp ≤ Sbig := le_trans hCp_le hS₁le
    have hβ_le_big : psiBeta ≤ Sbig := le_trans hβ_le hS₁le
    have hK_le_big : K ≤ Sbig := by
      have h5 : K ≤ 5 * (S₁ + 1) ^ 3 := by
        have h6 : (2 * (S₁ + 1) + 4 : ℝ) ≤ 5 * (S₁ + 1) ^ 3 := by
          have h7 : (2:ℝ) ≤ S₁ + 1 := by linarith only [hS₁1]
          have h7b : (0:ℝ) < S₁ + 1 := by linarith only [hS₁1]
          have e1 : 2 * (S₁ + 1) + 4 ≤ 6 * (S₁ + 1) := by linarith only [h7]
          have e2 : (6:ℝ) ≤ 5 * (S₁ + 1) ^ 2 := by nlinarith only [h7]
          have e3 : 6 * (S₁ + 1) ≤ 5 * (S₁ + 1) ^ 3 := by
            have hh := mul_le_mul_of_nonneg_right e2 (le_of_lt h7b)
            calc 6 * (S₁ + 1) ≤ (5 * (S₁ + 1) ^ 2) * (S₁ + 1) := hh
              _ = 5 * (S₁ + 1) ^ 3 := by ring
          linarith only [e1, e3]
        have h6' : 2 * S₁ + 4 ≤ 2 * (S₁ + 1) + 4 := by linarith only [hS₁0]
        exact le_trans hK_le (le_trans h6' h6)
      rw [hSbig]
      have h8 : (5:ℝ) * (S₁ + 1) ^ 3 ≤ 10 ^ 40 * (S₁ + 1) ^ 3 + 1 := by
        have h9 : (5:ℝ) * (S₁ + 1) ^ 3 ≤ 10 ^ 40 * (S₁ + 1) ^ 3 :=
          mul_le_mul_of_nonneg_right (by norm_num : (5:ℝ) ≤ 10^40) (pow_nonneg (by linarith only [hS₁0]) 3)
        linarith only [h9]
      linarith only [h5, h8]
    -- ### `Sbig` dominates the numerical thresholds used by Route-B assembly
    have hSbig200 : (200 : ℝ) ≤ Sbig := by
      have h := sbig_ge_mul_of_le (X := 1) (c := 200) hSbig (by norm_num) hS₁1 hS₁0
        (by norm_num) (by norm_num)
      simpa using h
    have hSbig48 : 48 * psiBeta ≤ Sbig :=
      sbig_ge_mul_of_le hSbig hβ0 hβ_le hS₁0 (by norm_num) (by norm_num)
    have hSbig72 : 72 * psiBeta ≤ Sbig :=
      sbig_ge_mul_of_le hSbig hβ0 hβ_le hS₁0 (by norm_num) (by norm_num)
    have hSbigC2 : 10 ^ 14 * C₂ ≤ Sbig :=
      sbig_ge_mul_of_le hSbig hC₂.le hC₂_le hS₁0 (by norm_num) (by norm_num)
    have hSbigD : 10 ^ 39 * D ≤ Sbig :=
      sbig_ge_mul_of_le hSbig hD.le hD_le hS₁0 (by norm_num) (by norm_num)
    have hSbigCp : 22 * 10 ^ 17 * Cp ≤ Sbig :=
      sbig_ge_mul_of_le hSbig hCp.le hCp_le hS₁0 (by norm_num) (by norm_num)
    have hSbigCK2 : 2 * 10 ^ 16 * (C * K) ≤ Sbig := by
      refine sbig_ge_mul_of_sq_le (X := C * K) (c := 2 * 10 ^ 16) hSbig (by positivity) ?_
        hS₁0 (by norm_num) (by norm_num)
      have hK0' : 0 ≤ K := by linarith only [hK1]
      have ha : C * K ≤ S₁ * (2 * S₁ + 4) := by
        calc C * K ≤ S₁ * K := mul_le_mul_of_nonneg_right hC_le hK0'
          _ ≤ S₁ * (2 * S₁ + 4) := mul_le_mul_of_nonneg_left hK_le hS₁0
      have hb : S₁ * (2 * S₁ + 4) ≤ 6 * (S₁ + 1) ^ 2 := by nlinarith only [hS₁0]
      linarith only [ha, hb]
    set L : ℝ := Real.log (T + 3) + 1 with hL
    have hL0 : 0 ≤ L := by
      rw [hL]; exact add_nonneg (Real.log_nonneg (by linarith only [hT5])) zero_le_one
    have hL1 : 1 ≤ L := by
      rw [hL]; have h := Real.log_nonneg (by linarith only [hT5] : (1:ℝ) ≤ T+3); linarith only [h]
    have hL_le : L ≤ 20000 * Real.log x := by
      have hT0pos : 0 < T₀ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 5) hT₀5
      have hsqrtpos : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hYpos
      have hlogT₀ : Real.log T₀ = Real.log Y / 2 + 100 * Real.log (Real.log Y) := by
        rw [hT₀, Real.log_mul (ne_of_gt hsqrtpos) (pow_ne_zero 100 (ne_of_gt (by linarith only [hlogYge] : (0:ℝ) < Real.log Y))),
          Real.log_pow, Real.log_sqrt (le_of_lt hYpos)]
        push_cast; ring
      have hll : Real.log (Real.log Y) ≤ 101 * Real.log x := by
        have h7 : (0 : ℝ) < Real.log Y := by linarith only [hlogYge]
        have h8 : Real.log (Real.log Y) ≤ Real.log Y := by
          have := Real.log_le_sub_one_of_pos h7
          linarith only [this]
        linarith only [h8, hlogYle]
      have hlog2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
        exact le_of_lt Real.exp_one_gt_two
      have hlogT : Real.log T ≤ Real.log T₀ + 2 := by
        have h1 : Real.log T ≤ Real.log (T₀ + 1) := Real.log_le_log hT0 (by linarith only [hThi])
        have h2 : Real.log (T₀ + 1) ≤ Real.log (2 * T₀) :=
          Real.log_le_log (by linarith only [hT₀5]) (by linarith only [hT₀5])
        have h3 : Real.log (2 * T₀) = Real.log 2 + Real.log T₀ :=
          Real.log_mul (by norm_num) (by linarith only [hT₀5])
        linarith only [h1, h2, h3, hlog2]
      have hlogT3 : Real.log (T + 3) ≤ Real.log T + 2 := by
        have h1 : T + 3 ≤ 4 * T := by linarith only [hT5]
        have h2 : Real.log (T + 3) ≤ Real.log (4 * T) := Real.log_le_log (by linarith only [hT5]) h1
        have h3 : Real.log (4 * T) = Real.log 4 + Real.log T :=
          Real.log_mul (by norm_num) (by linarith only [hT5])
        have h4 : Real.log 4 ≤ 2 := by
          rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
          have := Real.log_two_lt_d9
          linarith only [this]
        linarith only [h1, h2, h3, h4]
      rw [hL]
      linarith only [hlogT3, hlogT, hlogT₀, hll, hlogYle, hLx1]
    -- ## the good-height gap and `K·L·δ ≥ 1`
    have hn_bound : (n : ℝ) ≤ c₀ * (Real.log T₀ + 1) + 1 := by
      have h1 : (Sw.card : ℝ) ≤ c₀ * (Real.log T₀ + 1) := hScard
      have h2 : (n : ℝ) = (Sw.card : ℝ) + 1 := by rw [hn]; push_cast; ring
      linarith only [h1, h2]
    have hKδ : (1 : ℝ) ≤ K * L * δ := by
      have hlogT₀1 : (1 : ℝ) ≤ Real.log T₀ + 1 := by
        have hh : (0:ℝ) ≤ Real.log T₀ := Real.log_nonneg (by linarith only [hT₀5])
        linarith only [hh]
      have hLge : Real.log T₀ + 1 ≤ L := by
        rw [hL]
        have h1 : Real.log T₀ ≤ Real.log (T + 3) :=
          Real.log_le_log (by linarith only [hT₀5]) (by linarith only [hTlo])
        linarith only [h1]
      have hnum : (2 * c₀ + 4) * (Real.log T₀ + 1) ≤ K * L := by
        rw [hK]
        exact mul_le_mul le_rfl hLge (by linarith only [hlogT₀1]) (by linarith only [hc₀.le])
      have hden : 2 * (n : ℝ) + 2 ≤ 2 * c₀ * (Real.log T₀ + 1) + 4 := by linarith only [hn_bound]
      have hdenpos : 0 < 2 * (n : ℝ) + 2 := h2n
      have hBpos : 0 < 2 * c₀ * (Real.log T₀ + 1) + 4 := by
        have : (0:ℝ) ≤ 2 * c₀ * (Real.log T₀ + 1) :=
          mul_nonneg (mul_nonneg (by norm_num) hc₀.le) (by linarith only [hlogT₀1])
        linarith only [this]
      have hgoal : (2 * c₀ + 4) * (Real.log T₀ + 1)
          ≤ K * L * (2 * (n : ℝ) + 2) := by
        have hKL0 : 0 ≤ K * L := mul_nonneg (by linarith only [hK1]) (by linarith only [hL1])
        have h2 : (1 : ℝ) ≤ 2 * (n : ℝ) + 2 := by
          have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        calc (2 * c₀ + 4) * (Real.log T₀ + 1) ≤ K * L := hnum
          _ = K * L * 1 := by ring
          _ ≤ K * L * (2 * (n : ℝ) + 2) := mul_le_mul_of_nonneg_left h2 hKL0
      rw [hδ, mul_one_div]
      rw [le_div_iff₀ hdenpos]
      linarith [hgoal]
    -- ## the gap and `hgood`
    have hgapT : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T| := by
      intro ρ hζ
      by_cases hwin' : T₀ - 1 ≤ ρ.im ∧ ρ.im ≤ T₀ + 2
      · have hmem : ρ.im ∈ Sw := by
          have him0 : ρ.im ≠ 0 := by linarith [hT₀5, hwin'.1]
          have hρ1 : ρ ≠ 1 := by
            intro h1
            rw [h1] at him0
            simp at him0
          have hζz : riemannZeta ρ = 0 := by
            rw [riemannZeta_eq_inv_sub_mul hρ1, hζ, mul_zero]
          have hmass : ¬∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
            rintro ⟨n, hn⟩
            have hre : ρ.im = 0 := by rw [hn]; simp
            exact him0 hre
          exact hSword ρ hζz (h ρ hζz hmass hρ1) hwin'.1 hwin'.2
        have hg := hTgap ρ.im hmem
        rwa [abs_sub_comm] at hg
      · have hwin'' : ¬(T₀ - 1 ≤ ρ.im) ∨ ¬(ρ.im ≤ T₀ + 2) := not_and_or.mp hwin'
        rcases hwin'' with hlt | hgt
        · have hlt' : ρ.im < T₀ - 1 := lt_of_not_ge hlt
          have h1 : (1 : ℝ) ≤ |ρ.im - T| := by
            rw [abs_of_nonpos (by linarith only [hlt', hTlo])]
            linarith only [hlt', hTlo]
          linarith only [h1, hδle]
        · have hgt' : T₀ + 2 < ρ.im := lt_of_not_ge hgt
          have h1 : (1 : ℝ) ≤ |ρ.im - T| := by
            rw [abs_of_pos (by linarith only [hgt', hThi])]
            linarith only [hgt', hThi]
          linarith only [h1, hδle]
    have hgoodT : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ T ∧ ρ.im ≠ -T := by
      intro ρ hζ
      constructor
      · intro him
        have h1 := hgapT ρ hζ
        rw [him, sub_self, abs_zero] at h1
        linarith
      · intro him
        have hconj : riemannZeta₁ (conj ρ) = 0 := by
          rw [riemannZeta₁_conj, hζ, map_zero]
        have h1 := hgapT (conj ρ) hconj
        have h2 : (conj ρ).im = T := by rw [Complex.conj_im, him, neg_neg]
        rw [h2, sub_self, abs_zero] at h1
        linarith
    -- ## the zero set
    have hRz : (0 : ℝ) ≤ 2 + |T| := add_nonneg (by norm_num) (abs_nonneg T)
    set Zstar : Finset ℂ := (zetaZeroBallFin (2 + |T|) hRz).filter
      (fun ρ => ρ.re = 1 / 2 ∧ |ρ.im| < T) with hZstar
    have hZmem : ∀ ρ ∈ Zstar,
        ρ.re = 1 / 2 ∧ |ρ.im| < T ∧ riemannZeta₁ ρ = 0 ∧ ‖ρ‖ ≤ 2 + |T| := by
      intro ρ hρ
      rw [hZstar, Finset.mem_filter] at hρ
      obtain ⟨hball, hre, him⟩ := hρ
      obtain ⟨hbb, hζ⟩ := (zetaZeroBallFin_spec (2 + |T|) hRz ρ).mp hball
      have hnorm : ‖ρ‖ ≤ 2 + |T| := by
        rw [Metric.mem_closedBall, dist_zero_right] at hbb
        exact hbb
      exact ⟨hre, him, hζ, hnorm⟩
    have hZre : ∀ ρ ∈ Zstar, (1 / 4 : ℝ) < ρ.re ∧ ρ.re < 2 := by
      intro ρ hρ
      obtain ⟨hre, _, _, _⟩ := hZmem ρ hρ
      constructor <;> linarith
    have hZr : ∀ ρ ∈ Zstar, ρ.re = (1 / 2 : ℝ) := fun ρ hρ => (hZmem ρ hρ).1
    -- ## the pointwise bound
    have hpt : ∀ t : ℝ, x ≤ t → t ≤ Y →
        ‖(Chebyshev.psi t : ℂ) - ((t : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
            ∑ ρ ∈ Zstar, (zeta1Order ρ : ℂ) * (t : ℂ) ^ ρ / ρ)‖ ≤
          C * (t * L ^ 3 / T) * K +
          C₂ * (L * (min 1 (2 * t / (T * |t - (Nat.floor t : ℝ)|)) +
            min 1 (2 * t / (T * |t - ((Nat.floor t : ℝ) + 1)|)))) +
          (if (Nat.floor t : ℝ) = t then 4 * L else 0) +
          D * (t ^ (-(3 / 2) : ℝ) * L ^ 4) := by
      intro t hxt htY
      have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hx1 hxt
      have htpos : 0 < t := lt_trans one_pos ht1
      have hlogt1 : (1 : ℝ) ≤ Real.log t := by
        have := Real.log_le_log hxpos hxt
        linarith
      have htt : t ≤ T ^ 2 := le_trans htY hT2Y
      have hmain := hform t (le_trans hxx1 hxt) T δ K hT5 htt hδ0 hK1 hKδ hgapT hgoodT
      rw [zRectZeros_eq_filter h hRz
        (by norm_num : (-2:ℝ) < -(3/2)) (by norm_num : (-(3/2):ℝ) < 1/2)
        (by have h0 : 0 < 1 / Real.log t := one_div_pos.mpr (by linarith : 0 < Real.log t)
            linarith)] at hmain
      simpa only [hL, hZstar] using hmain
    -- ═══════════════ ROUTE-B ASSEMBLY ═══════════════
    have hβ0' : 0 ≤ psiBeta := hβ0
    have hYeq' : Y = x * (Real.log x) ^ 100 := hY
    have hK0' : 0 ≤ K := by linarith only [hK1]
    have hllT : Real.log (Real.log Y) ≤ 101 * Real.log x := by
      have h8 : Real.log (Real.log Y) ≤ Real.log Y := by
        have h9 := Real.log_le_sub_one_of_pos (by linarith only [hlogYge] : (0:ℝ) < Real.log Y)
        linarith only [h9]
      linarith only [h8, hlogYle]
    -- thresholds from `hthr`
    have hS48 : 48 * psiBeta / ε ≤ Real.log x :=
      hthr _ (by positivity) hSbig48
    have hS72 : 72 * psiBeta / ε ≤ Real.log x :=
      hthr _ (by positivity) hSbig72
    have hSCK2 : 2 * 10 ^ 16 * (C * K) / ε ≤ Real.log x :=
      hthr _ (by positivity) hSbigCK2
    -- (a) the dominated pointwise error bound
    have hE : ∀ t : ℝ, x ≤ t → t ≤ Y →
        ‖(((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Zstar t‖
          ≤ C * K * (L ^ 3 / T) * t + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) := by
      intro t hxt htY
      have h1 := hpt t hxt htY
      have h2 : (Chebyshev.psi t : ℂ) - ((t : ℂ) - Complex.log (2 * (Real.pi : ℂ)) -
            ∑ ρ ∈ Zstar, (zeta1Order ρ : ℂ) * (t : ℂ) ^ ρ / ρ)
          = (((Chebyshev.psi t - t : ℝ) : ℂ)) - Gc Zstar t := by
        rw [Gc]; push_cast; ring
      rw [h2] at h1
      have hle := ef_le_dominated (C := C) (C₂ := C₂) (D := D) (K := K) (L := L) (T := T)
        (x := x) (t := t) hC₂.le hD.le hL0 (rpow_neg_three_halves_le hxpos hxt)
      linarith only [h1, hle]
    -- (b) integrability, tail, the zero set
    have hInt : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Chebyshev.psi t - t) * psiKw t) (Set.Ioi x) := by
      simpa only [psiKw] using hxi0 x hxxi0
    have hTail : ∀ Y' : ℝ, Y ≤ Y' → |∫ t in Set.Ioi Y', ((Chebyshev.psi t : ℝ) - t)
        * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))|
        ≤ Cp * (Real.log Y') ^ 9 / Y' ^ (1 / 2 : ℝ) :=
      fun Y' hY' => htail Y' (le_trans hxYt (le_trans hxY hY'))
    have hρ : ∀ ρ ∈ Zstar, ρ.re = (1 / 2 : ℝ) := fun ρ hρmem => (hZmem ρ hρmem).1
    have hβ : ∑ ρ ∈ Zstar, (zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2 ≤ psiBeta := by
      refine zeta1Order_sum_le_psiBeta h hRz Zstar (fun ρ hρmem => ?_)
      obtain ⟨ha, hb, hc, hd⟩ := hZmem ρ hρmem
      obtain ⟨he, hf⟩ := hZre ρ hρmem
      exact ⟨hc, hd, he, hf⟩
    -- (c) the exponential thresholds
    have hSbigHalves : (Sbig / 2) / ε ≤ Real.log x / 2 := by
      have hh : Sbig / ε ≤ Real.log x := hthr Sbig (by linarith only [hSbig200]) le_rfl
      have h2 : Sbig / ε / 2 ≤ Real.log x / 2 := div_le_div_of_nonneg_right hh (by norm_num)
      have e : (Sbig / 2) / ε = Sbig / ε / 2 := by rw [div_div, div_div, mul_comm]
      linarith only [e, h2]
    have hSbigHalvesL : (Sbig / 2) / ε ≤ Real.log x := by
      have hh : Sbig / ε ≤ Real.log x := hthr Sbig (by linarith only [hSbig200]) le_rfl
      have h0 : (0 : ℝ) ≤ Sbig / ε := div_nonneg (by linarith only [hSbig200]) hε.le
      have h2 : Sbig / ε / 2 ≤ Real.log x := by linarith only [hh, h0]
      have e : (Sbig / 2) / ε = Sbig / ε / 2 := by rw [div_div, div_div, mul_comm]
      linarith only [e, h2]
    have hX1 : 48 / ε ≤ x ^ (1 / 2 : ℝ) := le_rpow_half_of_le_div_sq hε hxbig
    have hX2 : 288 * L / ε ≤ x ^ (1 / 2 : ℝ) := by
      rw [rpow_half_eq_exp x hxpos]
      exact exp_half_ge_L hε hε1 hSbig200 hL0 hL_le hSbigHalves
    have hX3 : 144 * C₂ * L / ε ≤ x ^ (1 / 2 : ℝ) := by
      rw [rpow_half_eq_exp x hxpos]
      exact exp_half_ge_C2L hε hε1 hSbig200 hC₂.le hSbigC2 hL0 hL_le hSbigHalves
    have hX4 : 144 * D * L ^ 4 / ε ≤ x ^ 2 := by
      rw [← exp_two_log_eq_sq x hxpos]
      exact exp_two_log_ge_DL4 hε hε1 hSbig200 hD.le hSbigD hL0 hL_le (le_of_lt hLx0)
        hSbigHalvesL
    -- (d) the two numerical side conditions
    have htailnum : Cp * (Real.log Y) ^ 9 / Y ^ (1 / 2 : ℝ)
        ≤ (ε / 2) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) :=
      psi_assembly_tailnum hCp.le hε hx2 hxY hLx100 hYeq' hlogYle hthr
        (by nlinarith only [hSbigCp])
    have hmainnum : ‖Complex.log (2 * (Real.pi : ℂ))‖ * (2 / (x * Real.log x))
        + psiBeta * (2 * qX x * cfX x + 2 * qX Y * cfX Y)
        + C * K * (L ^ 3 / T) * (2 * (Real.log (Real.log Y) - Real.log (Real.log x)))
        + (2 * C₂ * L + 4 * L + D * (x ^ (-(3 / 2) : ℝ) * L ^ 4)) * (2 / (x * Real.log x))
        ≤ (2 * psiBeta + ε / 2) * (1 / (x ^ (1 / 2 : ℝ) * Real.log x)) :=
      psi_assembly_mainnum hx2 hxY (by linarith only [hT5] : (1 : ℝ) ≤ T) hL0 hK0'
        hC.le hC₂.le hD.le hε hβ0'
        complex_log_two_pi_norm_le_two hLx100 hL_le hYeq' hTlo hlogYle hllT
        hS48 hS72 hSCK2 hX1 hX2 hX3 hX4
    exact psi_integral_assembly h hCp.le hC.le hC₂.le hD.le hx2 hxe hxY
      (by linarith only [hT5] : (1 : ℝ) ≤ T) hK0' hL0 hε
      hρ hβ hE hInt hTail htailnum hmainnum
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨x₀, hx₀⟩

end Commons.NumberTheory.Zeta
