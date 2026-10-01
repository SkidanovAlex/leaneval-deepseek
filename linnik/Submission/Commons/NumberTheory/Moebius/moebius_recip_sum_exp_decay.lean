import Mathlib
import Submission.Commons.Analysis.Fourier.perronStep_deviation
import Submission.Commons.NumberTheory.Zeta.zeta_inv_le_logPow_zeroFree
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.NumberTheory.Zeta.mangoldt_perron_sum_eq
import Submission.Commons.NumberTheory.Moebius.moebius_abs_le_one
import Submission.Commons.NumberTheory.Moebius.recip_perron_error_sum_le
import Submission.Commons.NumberTheory.Zeta.perronOne_bound
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
import Submission.Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le

namespace Commons.NumberTheory.Moebius

open scoped BigOperators Topology
open Complex MeasureTheory intervalIntegral Filter

noncomputable section

set_option maxHeartbeats 1000000

/-- The (truncated) Perron step integral
`perronStep σ T z = (1/2π) ∫_{-T}^{T} exp((σ+it)·log z)/(σ+it) dt`. -/
def perronStep (σ T z : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t in -T..T,
    Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * Complex.log (z : ℂ)) /
      ((σ : ℂ) + Complex.I * (t : ℂ))

/-! ## 1. The Perron step for positive `σ`

The truncated Perron step is
`perronStep σ T z = (1/2π) ∫_{-T}^{T} exp((σ+it)·log z)/(σ+it) dt`.
Its limit as `T → ∞` (for `σ > 0`) is `1` when `z > 1` and `0` when `0 < z < 1`; we
need the deviation bound for *positive* (not necessarily `≥ 1`) `σ`, which the
committed `Commons.Analysis.Fourier.perronStep_deviation` only provides for `1 ≤ σ`.
Everything in its proof (the σ-shifted Perron-kernel bounds) is valid for `σ > 0`. -/

/-- **Small-`σ` truncated Perron kernel deviation.**  For `0 < σ`, `1 ≤ T` and `α ≠ 0`,
`‖pskInt σ T α − (if 0 < α then 2π e^{−σα} else 0)‖ ≤ 32 · min 1 (1/(T|α|))`. -/
lemma pskInt_dev_of_pos (σ T α : ℝ) (hσ : 0 < σ) (hT : 1 ≤ T) (hα : α ≠ 0) :
    ‖Commons.Analysis.Fourier.pskInt σ T α -
        (if 0 < α then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0)‖
      ≤ 32 * min 1 (1 / (T * |α|)) := by
  let V : ℂ := if 0 < α then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0
  have hconv : Tendsto (fun R : ℝ => Commons.Analysis.Fourier.pskInt σ R α) atTop (𝓝 V) := by
    simpa [V, Commons.Analysis.Fourier.pskInt, Commons.Analysis.Fourier.pskKern] using
      (Commons.Analysis.Fourier.perronKernelSigma_tendsto σ α hσ hα)
  have hδpos : 0 < T * |α| := mul_pos (lt_of_lt_of_le zero_lt_one hT) (abs_pos.mpr hα)
  by_cases hδle : T * |α| ≤ 1
  · have hmin : min 1 (1 / (T * |α|)) = 1 := by
      rw [min_eq_left]
      rw [one_le_div₀ hδpos]
      exact hδle
    rw [hmin]
    have hreg : ‖Commons.Analysis.Fourier.pskInt σ T α‖ ≤ Real.pi + 2 := by
      have hb : ‖Commons.Analysis.Fourier.pskInt σ T α‖ ≤ Real.pi + 2 * |α| * T := by
        simpa [Commons.Analysis.Fourier.pskInt, Commons.Analysis.Fourier.pskKern] using
          (Commons.Analysis.Fourier.perronKernelSigma_regionBound σ T α hσ
            (le_trans zero_le_one hT))
      have hbt : 2 * |α| * T ≤ 2 := by nlinarith
      nlinarith
    have hVnorm : ‖V‖ ≤ 2 * Real.pi := by
      simpa [V] using Commons.Analysis.Fourier.psk_value_norm σ α hσ
    have hmain : ‖Commons.Analysis.Fourier.pskInt σ T α - V‖ ≤ 32 := by
      calc
        ‖Commons.Analysis.Fourier.pskInt σ T α - V‖
            ≤ ‖Commons.Analysis.Fourier.pskInt σ T α‖ + ‖V‖ := norm_sub_le _ _
        _ ≤ (Real.pi + 2) + 2 * Real.pi := add_le_add hreg hVnorm
        _ ≤ 32 := by nlinarith [Real.pi_lt_four]
    simpa using hmain
  · have hδgt1 : 1 < T * |α| := lt_of_not_ge hδle
    have hmin : min 1 (1 / (T * |α|)) = 1 / (T * |α|) := by
      rw [min_eq_right]
      rw [div_le_one₀ hδpos]
      exact le_of_lt hδgt1
    rw [hmin]
    have htail : ∀ R : ℝ, T ≤ R →
        ‖Commons.Analysis.Fourier.pskInt σ R α - Commons.Analysis.Fourier.pskInt σ T α‖
          ≤ 6 / (|α| * T) := by
      intro R hR
      exact Commons.Analysis.Fourier.psk_tail_bound σ T R α hσ hα hT hR
    have hmain : ‖Commons.Analysis.Fourier.pskInt σ T α - V‖ ≤ 6 / (|α| * T) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hconvε : ∀ᶠ R in atTop,
          ‖Commons.Analysis.Fourier.pskInt σ R α - V‖ < ε := by
        have hh := (Metric.tendsto_nhds.mp hconv) ε hε
        simpa [dist_eq_norm] using hh
      rcases eventually_atTop.1 hconvε with ⟨R0, hR0⟩
      let R1 := max T R0
      have hTR1 : T ≤ R1 := le_max_left _ _
      have hR0R1 : R0 ≤ R1 := le_max_right _ _
      have hεR : ‖Commons.Analysis.Fourier.pskInt σ R1 α - V‖ ≤ ε :=
        (hR0 R1 hR0R1).le
      have htri : ‖Commons.Analysis.Fourier.pskInt σ T α - V‖ ≤
          ‖Commons.Analysis.Fourier.pskInt σ T α - Commons.Analysis.Fourier.pskInt σ R1 α‖ +
            ‖Commons.Analysis.Fourier.pskInt σ R1 α - V‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle (Commons.Analysis.Fourier.pskInt σ T α)
          (Commons.Analysis.Fourier.pskInt σ R1 α) V
      calc
        ‖Commons.Analysis.Fourier.pskInt σ T α - V‖
            ≤ ‖Commons.Analysis.Fourier.pskInt σ T α -
                  Commons.Analysis.Fourier.pskInt σ R1 α‖ +
                ‖Commons.Analysis.Fourier.pskInt σ R1 α - V‖ := htri
        _ ≤ 6 / (|α| * T) + ε := add_le_add
            (by rw [norm_sub_rev]; exact htail R1 hTR1) hεR
    have hmain' : ‖Commons.Analysis.Fourier.pskInt σ T α - V‖ ≤ 6 / (T * |α|) := by
      simpa [mul_comm] using hmain
    have hcmp : 6 / (T * |α|) ≤ 32 * (1 / (T * |α|)) := by
      rw [div_eq_mul_inv]
      rw [one_div]
      exact mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 32)
        (by positivity : 0 ≤ (T * |α|)⁻¹)
    simpa [V] using hmain'.trans hcmp

/-- **Perron step deviation for positive `σ`.**  For `0 < σ`, `1 ≤ T`, `0 < z ≠ 1`,
`‖perronStep σ T z − 1_{z>1}‖ ≤ (32/2π) z^σ min 1 (1/(T|log z|))`. -/
theorem perronStep_dev_of_pos (σ T z : ℝ) (hσ : 0 < σ) (hT : 1 ≤ T) (hz : 0 < z)
    (hz1 : z ≠ 1) :
    ‖perronStep σ T z - (if 1 < z then (1 : ℂ) else 0)‖
      ≤ (32 / (2 * Real.pi)) * (z ^ σ) * min 1 (1 / (T * |Real.log z|)) := by
  have hα : Real.log z ≠ 0 := by
    intro h0
    apply hz1
    have hzexp : Real.exp (Real.log z) = z := Real.exp_log hz
    calc
      z = Real.exp (Real.log z) := hzexp.symm
      _ = 1 := by rw [h0]; norm_num
  have hb32 : ‖Commons.Analysis.Fourier.pskInt σ T (Real.log z)
        - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
      ≤ 32 * min 1 (1 / (T * |Real.log z|)) :=
    pskInt_dev_of_pos σ T (Real.log z) hσ hT hα
  have hJ : (∫ (t : ℝ) in -T..T,
        Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ)))
          / ((σ : ℂ) + Complex.I * (t : ℂ)))
      = ((z ^ σ : ℝ) : ℂ) * Commons.Analysis.Fourier.pskInt σ T (Real.log z) := by
    have hfun : (fun t : ℝ =>
          Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ)))
            / ((σ : ℂ) + Complex.I * (t : ℂ)))
        = fun t : ℝ => ((z ^ σ : ℝ) : ℂ) *
            Commons.Analysis.Fourier.pskKern σ (Real.log z) t := by
      funext t
      exact Commons.Analysis.Fourier.perronStep_integrand_eq σ z t hz
    rw [hfun, intervalIntegral.integral_const_mul]
    rfl
  have hW : (if 1 < z then (1 : ℂ) else 0)
      = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
          (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
    by_cases hpos : 0 < Real.log z
    · have hzgt1 : 1 < z := (Real.log_pos_iff hz.le).mp hpos
      rw [if_pos hzgt1, if_pos hpos]
      have hreal : z ^ σ * Real.exp (-(σ * Real.log z)) = 1 := by
        calc z ^ σ * Real.exp (-(σ * Real.log z))
            = Real.exp (Real.log z * σ) * Real.exp (-(σ * Real.log z)) := by
                rw [Real.rpow_def_of_pos hz σ]
        _ = Real.exp (σ * Real.log z) * Real.exp (-(σ * Real.log z)) := by
              congr 2
              ring
        _ = 1 := by
              rw [← Real.exp_add]
              norm_num
      have hRHS : ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
            (2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z)))) = 1 := by
        calc
          ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
              (2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))))
              = (((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) * (2 * ↑Real.pi)) *
                  cexp (-((σ : ℂ) * ↑(Real.log z))) := by ring
          _ = ((↑((z ^ σ / (2 * Real.pi)) * (2 * Real.pi)) : ℂ)) *
                  cexp (-((σ : ℂ) * ↑(Real.log z))) := by
                have h2 : (2 : ℂ) * ↑Real.pi = (↑(2 * Real.pi) : ℂ) := by norm_num
                rw [h2, ← Complex.ofReal_mul]
          _ = ((z ^ σ : ℝ) : ℂ) * cexp (-((σ : ℂ) * ↑(Real.log z))) := by
                congr 1
                congr 1
                field_simp
          _ = ((z ^ σ : ℝ) : ℂ) * (Real.exp (-(σ * Real.log z)) : ℂ) := by
                have harg : -(((σ : ℂ) * ↑(Real.log z))) = (↑(-(σ * Real.log z)) : ℂ) := by
                  rw [← Complex.ofReal_mul]
                  norm_num
                rw [harg, ← Complex.ofReal_exp]
          _ = 1 := by
                rw [← Complex.ofReal_mul, hreal]
                norm_num
      rw [hRHS]
    · have hneg : ¬ 1 < z := by
        intro hzgt1
        exact hpos ((Real.log_pos_iff hz.le).mpr hzgt1)
      rw [if_neg hneg, if_neg hpos]
      simp
  have hbase : (1 / (2 * Real.pi)) * ((↑(z ^ σ : ℝ) : ℂ) *
          Commons.Analysis.Fourier.pskInt σ T (Real.log z))
        - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
            (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)
      = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
          (Commons.Analysis.Fourier.pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)) := by
    calc
      (1 / (2 * Real.pi)) * ((↑(z ^ σ : ℝ) : ℂ) *
            Commons.Analysis.Fourier.pskInt σ T (Real.log z))
          - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
              (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)
          = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((↑(z ^ σ : ℝ) : ℂ) *
                Commons.Analysis.Fourier.pskInt σ T (Real.log z))
              - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
                simp
          _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) * (↑(z ^ σ : ℝ) : ℂ)) *
                  Commons.Analysis.Fourier.pskInt σ T (Real.log z)
              - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
                ring
          _ = (↑((1 / (2 * Real.pi)) * z ^ σ) : ℂ) *
                  Commons.Analysis.Fourier.pskInt σ T (Real.log z)
              - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
                rw [← Complex.ofReal_mul]
          _ = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  Commons.Analysis.Fourier.pskInt σ T (Real.log z)
              - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
                congr 1
                congr 1
                field_simp
          _ = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
              (Commons.Analysis.Fourier.pskInt σ T (Real.log z)
                - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)) := by
                rw [mul_sub]
  have hcontent : perronStep σ T z - (if 1 < z then (1 : ℂ) else 0)
      = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
          (Commons.Analysis.Fourier.pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)) := by
    unfold perronStep
    rw [hJ, hW]
    exact hbase
  have hscal_nonneg : 0 ≤ z ^ σ / (2 * Real.pi) := by positivity
  have hnormfac : ‖(((z ^ σ / (2 * Real.pi) : ℝ) : ℂ)) *
            (Commons.Analysis.Fourier.pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0))‖
        = (z ^ σ / (2 * Real.pi)) *
            ‖Commons.Analysis.Fourier.pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖ := by
    calc
      ‖(((z ^ σ / (2 * Real.pi) : ℝ) : ℂ)) *
            (Commons.Analysis.Fourier.pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0))‖
          = ‖(((z ^ σ / (2 * Real.pi) : ℝ) : ℂ))‖ *
              ‖Commons.Analysis.Fourier.pskInt σ T (Real.log z)
                - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖ :=
                norm_mul _ _
      _ = |z ^ σ / (2 * Real.pi)| *
            ‖Commons.Analysis.Fourier.pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖ := by
            rw [show ‖(((z ^ σ / (2 * Real.pi) : ℝ) : ℂ))‖ = |z ^ σ / (2 * Real.pi)| by
              simpa using (RCLike.norm_ofReal (K := ℂ) (z ^ σ / (2 * Real.pi)))]
      _ = (z ^ σ / (2 * Real.pi)) *
            ‖Commons.Analysis.Fourier.pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖ := by
            rw [abs_of_nonneg hscal_nonneg]
  have hfin : (z ^ σ / (2 * Real.pi)) * ‖Commons.Analysis.Fourier.pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
        ≤ (32 / (2 * Real.pi)) * z ^ σ * min 1 (1 / (T * |Real.log z|)) := by
    calc
      (z ^ σ / (2 * Real.pi)) * ‖Commons.Analysis.Fourier.pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
          ≤ (z ^ σ / (2 * Real.pi)) * (32 * min 1 (1 / (T * |Real.log z|))) :=
            mul_le_mul_of_nonneg_left hb32 hscal_nonneg
      _ = (32 / (2 * Real.pi)) * z ^ σ * min 1 (1 / (T * |Real.log z|)) := by ring
  rw [hcontent, hnormfac]
  exact hfin


/-! ## 2. The reciprocal Möbius Dirichlet series and the truncated Perron integral -/

/-- On `Re s > 1`, the `LSeries` of the Möbius function is `1/ζ(s)`. -/
lemma LSeries_moebius_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = (riemannZeta s)⁻¹ := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  exact eq_inv_of_mul_eq_one_right h

/-- `riemannZeta₁ (1+s) = s · ζ(1+s)` for `s ≠ 0`. -/
lemma riemannZeta₁_one_add (s : ℂ) (hs : s ≠ 0) :
    riemannZeta₁ (1 + s) = s * riemannZeta (1 + s) := by
  have hs1 : (1 : ℂ) + s ≠ 1 := by
    intro h
    exact hs (by linear_combination h)
  have h := riemannZeta_eq_inv_sub_mul (s := 1 + s) hs1
  have h2 : (1 : ℂ) + s - 1 = s := by ring
  rw [h2] at h
  rw [h]
  field_simp

/-- The truncated Perron integral of `1/ζ(1+s)` along the vertical line `Re s = σ`. -/
def recipPerron (x T σ : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t in -T..T,
    (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
      riemannZeta₁ (1 + ((σ : ℂ) + Complex.I * (t : ℂ)))

/-- Pointwise: for `Re s > 0`, `x^s/ζ₁(1+s) = (1/ζ(1+s))·x^s/s = L(μ)(1+s)·x^s/s`. -/
lemma recipIntegrand_eq (x : ℝ) (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    (x : ℂ) ^ s / riemannZeta₁ (1 + s) =
      LSeries (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (1 + s) * (x : ℂ) ^ s / s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have h1s : (1 : ℝ) < (1 + s).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hz : riemannZeta (1 + s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1s
  rw [LSeries_moebius_eq_inv_zeta h1s, riemannZeta₁_one_add s hs0]
  field_simp

/-- **Perron expansion.**  The truncated Perron integral of `1/ζ(1+s)` expands into the
per-step kernels evaluated at `x/n`, weighted by `μ(n)/n`. -/
theorem recipPerron_eq_tsum (x T : ℝ) (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) :
    recipPerron x T σ = ∑' n : ℕ,
      ((ArithmeticFunction.moebius n : ℂ) / (n : ℂ)) * perronStep σ T (x / (n : ℝ)) := by
  let v : ℕ → ℂ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  let c : ℂ := 1 / (2 * (Real.pi : ℂ))
  let s : ℝ → ℂ := Commons.NumberTheory.Zeta.sigmaLine σ
  have hscont : Continuous s := by
    simpa [s] using (Commons.NumberTheory.Zeta.sigmaLine_continuous σ)
  have hsnz : ∀ t : ℝ, s t ≠ 0 := by
    intro t
    simpa [s] using (Commons.NumberTheory.Zeta.sigmaLine_ne_zero σ (ne_of_gt hσ) t)
  have hsre : ∀ t : ℝ, 0 < (s t).re := by
    intro t
    simpa [s, Commons.NumberTheory.Zeta.sigmaLine] using hσ
  have hσnorm : ∀ t : ℝ, σ ≤ ‖s t‖ := by
    intro t
    simpa [s] using (Commons.NumberTheory.Zeta.sigmaLine_norm_ge σ hσ t)
  let logz : ℕ → ℂ := fun n => Commons.NumberTheory.Zeta.perronLog x n
  let Ffun : ℕ → ℝ → ℂ := fun n t => c * (v n / (n : ℂ)) * Complex.exp (s t * logz n) / s t
  -- per-term identity
  have hterm : ∀ (n : ℕ) (t : ℝ),
      LSeries.term v (1 + s t) n * (x : ℂ) ^ (s t) / s t =
        (v n / (n : ℂ)) * Complex.exp (s t * logz n) / s t := by
    intro n t
    by_cases hn : n = 0
    · subst hn
      simp [v, LSeries.term, ArithmeticFunction.map_zero]
    · have hn0 : (n : ℂ) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        exact hn
      have hq : (n : ℂ) ^ (s t) ≠ 0 := by
        rw [Complex.cpow_ne_zero_iff]
        exact Or.inl hn0
      rw [LSeries.term_of_ne_zero hn]
      have hcp : (n : ℂ) ^ (1 + s t) = (n : ℂ) * (n : ℂ) ^ (s t) := by
        rw [Complex.cpow_add (1 : ℂ) (s t) hn0, Complex.cpow_one]
      rw [hcp]
      have hxdiv : (x : ℂ) ^ (s t) / (n : ℂ) ^ (s t) = Complex.exp (s t * logz n) := by
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        rw [← Complex.ofReal_natCast n]
        rw [Commons.NumberTheory.Zeta.div_cpow_ofReal_div x (n : ℝ) (le_of_lt hx) hnR.le (s t),
            Commons.NumberTheory.Zeta.exp_cpow_ofReal_pos (x / (n : ℝ)) (by positivity) (s t)]
        rfl
      rw [← hxdiv]
      field_simp
  have hmid : ∀ t : ℝ,
      (∑' n : ℕ, (v n / (n : ℂ)) * Complex.exp (s t * logz n) / s t) =
        LSeries v (1 + s t) * (x : ℂ) ^ (s t) / s t := by
    intro t
    calc
      (∑' n : ℕ, (v n / (n : ℂ)) * Complex.exp (s t * logz n) / s t)
          = ∑' n : ℕ, LSeries.term v (1 + s t) n * (x : ℂ) ^ (s t) / s t := by
              refine tsum_congr fun n => ?_
              exact (hterm n t).symm
      _ = (∑' n : ℕ, LSeries.term v (1 + s t) n) * ((x : ℂ) ^ (s t) / s t) := by
              rw [← tsum_mul_right]
              refine tsum_congr fun n => ?_
              ring
      _ = LSeries v (1 + s t) * (x : ℂ) ^ (s t) / s t := by
              simp only [LSeries]
              ring
  have hpt : ∀ t : ℝ,
      (∑' n : ℕ, Ffun n t) = c * ((x : ℂ) ^ (s t) / riemannZeta₁ (1 + s t)) := by
    intro t
    have h := recipIntegrand_eq x hx (hsre t)
    calc
      (∑' n : ℕ, Ffun n t)
          = ∑' n : ℕ, c * ((v n / (n : ℂ)) * Complex.exp (s t * logz n) / s t) := by
              refine tsum_congr fun n => ?_
              simp only [Ffun]
              ring
      _ = c * (∑' n : ℕ, (v n / (n : ℂ)) * Complex.exp (s t * logz n) / s t) :=
              tsum_mul_left
      _ = c * (LSeries v (1 + s t) * (x : ℂ) ^ (s t) / s t) := by rw [hmid t]
      _ = c * ((x : ℂ) ^ (s t) / riemannZeta₁ (1 + s t)) := by rw [← h]
  -- pointwise norm bound on the summands
  have hbound : ∀ (n : ℕ) (t : ℝ),
      ‖Ffun n t‖ ≤ ‖c‖ * (1 / (n : ℝ)) * ((x / (n : ℝ)) ^ σ) / σ := by
    intro n t
    by_cases hn : n = 0
    · subst hn
      simp [Ffun, v, ArithmeticFunction.map_zero]
    · have hn0 : (n : ℂ) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        exact hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hexpn : ‖Complex.exp (s t * logz n)‖ = (x / (n : ℝ)) ^ σ := by
        simpa [s, logz] using
          (Commons.NumberTheory.Zeta.norm_exp_perronLog x hx n hn σ t)
      have hv1 : ‖v n‖ ≤ 1 := by
        simpa [v, Complex.norm_intCast] using Commons.NumberTheory.Moebius.moebius_abs_le_one n
      have hsge : σ ≤ ‖s t‖ := hσnorm t
      have hnorm : ‖Ffun n t‖ = ‖c‖ * (‖v n‖ / ‖(n : ℂ)‖) * (x / (n : ℝ)) ^ σ / ‖s t‖ := by
        simp only [Ffun, norm_div, norm_mul, hexpn]
      rw [hnorm]
      have h1 : ‖v n‖ / ‖(n : ℂ)‖ ≤ 1 / (n : ℝ) := by
        have hcast : ‖(n : ℂ)‖ = (n : ℝ) := by simp
        rw [hcast]
        exact div_le_div_of_nonneg_right hv1 (le_of_lt hnR)
      have h2 : 0 ≤ (x / (n : ℝ)) ^ σ := Real.rpow_nonneg (div_nonneg hx.le hnR.le) σ
      have h3 : (x / (n : ℝ)) ^ σ / ‖s t‖ ≤ (x / (n : ℝ)) ^ σ / σ :=
        div_le_div_of_nonneg_left h2 hσ hsge
      have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
      calc ‖c‖ * (‖v n‖ / ‖(n : ℂ)‖) * (x / (n : ℝ)) ^ σ / ‖s t‖
          = ‖c‖ * ((‖v n‖ / ‖(n : ℂ)‖) * ((x / (n : ℝ)) ^ σ / ‖s t‖)) := by ring
        _ ≤ ‖c‖ * ((1 / (n : ℝ)) * ((x / (n : ℝ)) ^ σ / σ)) := by
              refine mul_le_mul_of_nonneg_left ?_ hc0
              exact mul_le_mul h1 h3 (div_nonneg h2 (norm_nonneg _))
                (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
        _ = ‖c‖ * (1 / (n : ℝ)) * ((x / (n : ℝ)) ^ σ) / σ := by ring
  -- summability of the dominating sequence
  let b : ℕ → ℝ := fun n => ‖c‖ * (1 / (n : ℝ)) * ((x / (n : ℝ)) ^ σ) / σ
  have hb_nonneg : ∀ n : ℕ, 0 ≤ b n := by
    intro n
    dsimp [b]
    have h1 : 0 ≤ (x / (n : ℝ)) ^ σ :=
      Real.rpow_nonneg (div_nonneg hx.le (by positivity)) σ
    positivity
  have hb_summable : Summable b := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (1 + σ))⁻¹) :=
      (Real.summable_nat_rpow_inv).mpr (by linarith)
    have hmul : Summable (fun n : ℕ => (‖c‖ * x ^ σ / σ) * ((n : ℝ) ^ (1 + σ))⁻¹) :=
      hbase.mul_left _
    refine Summable.congr hmul fun n => ?_
    by_cases hn : n = 0
    · subst hn
      dsimp [b]
      have h1σ : (1 : ℝ) + σ ≠ 0 := by positivity
      simp only [Nat.cast_zero]
      rw [div_zero, div_zero, Real.zero_rpow (ne_of_gt hσ), Real.zero_rpow h1σ, inv_zero]
      ring
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hkey : (1 / (n : ℝ)) * ((x / (n : ℝ)) ^ σ) = x ^ σ * ((n : ℝ) ^ (1 + σ))⁻¹ := by
        rw [Real.div_rpow hx.le hnR.le, one_div, div_eq_mul_inv]
        rw [show (n : ℝ)⁻¹ * (x ^ σ * ((n : ℝ) ^ σ)⁻¹) =
            x ^ σ * ((n : ℝ)⁻¹ * ((n : ℝ) ^ σ)⁻¹) by ring]
        rw [← mul_inv]
        rw [show ((n : ℝ) * ((n : ℝ) ^ σ)) = ((n : ℝ) ^ (1 : ℝ)) * ((n : ℝ) ^ σ) by
          rw [Real.rpow_one]]
        rw [← Real.rpow_add hnR]
      dsimp [b]
      rw [show ‖c‖ * (1 / (n : ℝ)) * ((x / (n : ℝ)) ^ σ) / σ
            = ‖c‖ * ((1 / (n : ℝ)) * ((x / (n : ℝ)) ^ σ)) / σ by ring, hkey]
      ring
  -- continuity of the summands
  have hFC_cont : ∀ n : ℕ, Continuous (fun t : ℝ => Ffun n t) := by
    intro n
    simpa [Ffun] using
      (Commons.NumberTheory.Zeta.perronSummand_continuous (c * (v n / (n : ℂ))) (logz n)
        hscont hsnz)
  let FC : ℕ → C(ℝ, ℂ) := fun n => ContinuousMap.mk (fun t : ℝ => Ffun n t) (hFC_cont n)
  let K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc (-T) T, isCompact_uIcc⟩
  have hsup : ∀ n : ℕ, ‖(FC n).restrict K‖ ≤ b n := by
    intro n
    rw [ContinuousMap.norm_le (f := (FC n).restrict K) (C := b n) (hb_nonneg n)]
    intro y
    change ‖Ffun n (y : ℝ)‖ ≤ b n
    exact hbound n (y : ℝ)
  have hFC_sum : Summable (fun n : ℕ => ‖(FC n).restrict K‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hsup hb_summable
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (f := FC) hFC_sum
  have hterm_int : ∀ n : ℕ,
      (∫ t in -T..T, Ffun n t) =
        (v n / (n : ℂ)) * (c * ∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by
    intro n
    have : (fun t : ℝ => Ffun n t) =
        fun t : ℝ => (c * (v n / (n : ℂ))) * (Complex.exp (s t * logz n) / s t) := by
      funext t
      simp only [Ffun]
      ring
    rw [this, intervalIntegral.integral_const_mul]
    ring
  have hper_step : ∀ n : ℕ,
      c * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) = perronStep σ T (x / (n : ℝ)) := by
    intro n
    have hfun : (fun t : ℝ => Complex.exp (s t * logz n) / s t) =
        fun t : ℝ => Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) *
            Complex.log ((x / (n : ℝ) : ℝ) : ℂ)) / ((σ : ℂ) + Complex.I * (t : ℂ)) := by
      funext t
      simp only [s, logz, Commons.NumberTheory.Zeta.sigmaLine,
        Commons.NumberTheory.Zeta.perronLog]
    rw [hfun]
    simp only [perronStep]
    push_cast
    ring
  calc recipPerron x T σ
      = c * (∫ t in -T..T, (x : ℂ) ^ (s t) / riemannZeta₁ (1 + s t)) := by
          simp only [recipPerron, c, s, Commons.NumberTheory.Zeta.sigmaLine]
      _ = ∫ t in -T..T, (∑' n : ℕ, Ffun n t) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [hpt t]
      _ = ∑' n : ℕ, ∫ t in -T..T, Ffun n t := hswap.symm
      _ = ∑' n : ℕ, (v n / (n : ℂ)) *
            (c * ∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by
          refine tsum_congr fun n => hterm_int n
      _ = ∑' n : ℕ, (v n / (n : ℂ)) * perronStep σ T (x / (n : ℝ)) := by
          refine tsum_congr fun n => ?_
          rw [hper_step n]
      _ = ∑' n : ℕ, ((ArithmeticFunction.moebius n : ℂ) / (n : ℂ)) *
            perronStep σ T (x / (n : ℝ)) := by
          refine tsum_congr fun n => ?_
          simp only [v, Complex.ofReal_intCast]

/-! ## 3. The truncation error for the reciprocal Möbius sum -/

/-- `‖perronStep σ T 1‖ ≤ 1/2`. -/
lemma perronStep_one_norm {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    ‖perronStep σ T 1‖ ≤ 1 / 2 := by
  have h : perronStep σ T 1 = (1 / (2 * Real.pi)) *
      (∫ (t : ℝ) in -T..T, (1 : ℂ) / (((σ : ℂ) + Complex.I * (t : ℂ)))) := by
    unfold perronStep
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp
  rw [h]
  exact Commons.NumberTheory.Zeta.perronOne_bound σ T hσ hT

/-- The truncated Perron integral of `1/ζ(1+s)` approximates `Σ_{n ≤ x} μ(n)/n`, with
truncation error bounded by the per-step deviation sum plus a boundary term. -/
theorem recipPerron_sub_sum_le (x T : ℝ) (hx : 3 ≤ x) (hT : 2 ≤ T) (hTx : T ≤ x)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ)) - recipPerron x T σ‖ ≤
      (32 / (2 * Real.pi)) *
          (∑' n : ℕ, (1 / (n : ℝ)) * (x / (n : ℝ)) ^ σ *
            min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) +
        (3 / 2) * (1 / (⌊x⌋₊ : ℝ)) := by
  have hxpos : 0 < x := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  set f : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) with hfdef
  set g : ℕ → ℂ := fun n => f n * perronStep σ T (x / (n : ℝ)) with hgdef
  set err : ℕ → ℝ := fun n => (1 / (n : ℝ)) * (x / (n : ℝ)) ^ σ *
      min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) with herrdef
  let ind : ℕ → ℂ := fun n => if (n : ℝ) ≤ x then f n else 0
  -- norm bound for `f n`
  have hfn_le : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) → ‖f n‖ ≤ 1 / (n : ℝ) := by
    intro n hnR
    have h1 := Commons.NumberTheory.Moebius.moebius_abs_le_one n
    have hfn : ‖f n‖ = |(ArithmeticFunction.moebius n : ℝ)| / (n : ℝ) := by
      simp only [f, hfdef]
      rw [norm_div, Complex.norm_intCast, Complex.norm_natCast]
    rw [hfn]
    exact div_le_div_of_nonneg_right h1 hnR.le
  -- the finite sum equals the indicator sum
  have hindsum : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) = ∑' n : ℕ, ind n := by
    have h1 : (∑' n : ℕ, ind n) = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ind n := by
      apply tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.Icc 0 ⌊x⌋₊)
        (f := ind)
      intro n hn
      by_cases h : (n : ℝ) ≤ x
      · have hnfl : n ≤ ⌊x⌋₊ := Nat.le_floor h
        exact absurd (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnfl⟩) hn
      · simp only [ind]
        exact if_neg h
    have hI : Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hzero : ind 0 = 0 := by
      have h0 : ((0 : ℕ) : ℝ) ≤ x := by simp; linarith
      simp only [ind]
      rw [if_pos h0]
      simp [f, hfdef, ArithmeticFunction.map_zero]
    have hsum_eq : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ind n = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n := by
      rw [hI, Finset.sum_insert (by simp), hzero, zero_add]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnfl : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hn).2
      have hxle : (n : ℝ) ≤ x :=
        le_trans (by exact_mod_cast hnfl) (Nat.floor_le hxpos.le)
      simp only [ind]
      exact if_pos hxle
    exact h1.trans hsum_eq |>.symm
  -- `g` sums to the Perron integral
  have hgsum : (∑' n : ℕ, g n) = recipPerron x T σ := by
    rw [recipPerron_eq_tsum x T hxpos hσ]
  -- pointwise deviation bound
  have hpt : ∀ n : ℕ, ‖ind n - g n‖ ≤
      (32 / (2 * Real.pi)) * err n + (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hf0 : f 0 = 0 := by simp [f, hfdef, ArithmeticFunction.map_zero]
      have hind0 : ind 0 = 0 := by
        have h0 : ((0 : ℕ) : ℝ) ≤ x := by simp; linarith
        simp only [ind]
        rw [if_pos h0, hf0]
      have hg0 : g 0 = 0 := by simp only [g, hgdef, hf0, zero_mul]
      have herr0 : err 0 = 0 := by
        simp only [err, herrdef, Nat.cast_zero]
        simp [Real.zero_rpow (ne_of_gt hσ)]
      have hbd0 : (if (((0 : ℕ)) : ℝ) = x then (3 / 2) * (1 / ((0 : ℕ) : ℝ)) else 0) = 0 := by
        have h0x : (((0 : ℕ)) : ℝ) ≠ x := by
          simp only [Nat.cast_zero]; linarith
        rw [if_neg h0x]
      rw [hind0, hg0, herr0, hbd0]
      simp
    · have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hfnle := hfn_le n hnR
      have hzpos : 0 < x / (n : ℝ) := div_pos hxpos hnR
      by_cases hnx : (n : ℝ) = x
      · -- boundary case `n = x`
        have hind : ind n = f n := by
          simp only [ind]
          exact if_pos (le_of_eq hnx)
        have hgn : g n = f n * perronStep σ T 1 := by
          simp only [g, hgdef]
          rw [hnx, div_self (ne_of_gt hxpos)]
        have hper : ‖perronStep σ T 1‖ ≤ 1 / 2 := perronStep_one_norm hσ (by linarith)
        have herrzero : err n = 0 := by
          simp only [err, herrdef]
          rw [hnx, div_self (ne_of_gt hxpos), Real.one_rpow, Real.log_one, abs_zero, mul_zero,
            div_zero, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
          ring
        have hbd : (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0) =
            (3 / 2) * (1 / (n : ℝ)) := if_pos hnx
        rw [hbd]
        calc ‖ind n - g n‖ = ‖f n * ((1 : ℂ) - perronStep σ T 1)‖ := by
              rw [hind, hgn]
              ring_nf
          _ = ‖f n‖ * ‖(1 : ℂ) - perronStep σ T 1‖ := norm_mul _ _
          _ ≤ (1 / (n : ℝ)) * (3 / 2) := by
              refine mul_le_mul hfnle ?_ (norm_nonneg _) (by positivity)
              calc ‖(1 : ℂ) - perronStep σ T 1‖ ≤ ‖(1 : ℂ)‖ + ‖perronStep σ T 1‖ :=
                    norm_sub_le _ _
                _ ≤ 1 + 1 / 2 := by rw [norm_one]; linarith
                _ = 3 / 2 := by norm_num
          _ = (32 / (2 * Real.pi)) * err n + (3 / 2) * (1 / (n : ℝ)) := by
              rw [herrzero]; ring
      · -- main case
        have hI : (if (n : ℝ) < x then (1 : ℂ) else 0) =
            (if 1 < x / (n : ℝ) then (1 : ℂ) else 0) := by
          rcases lt_trichotomy (n : ℝ) x with h | h | h
          · have h2 : 1 < x / (n : ℝ) := by
              rw [lt_div_iff₀ hnR]; simpa using h
            simp [h, h2]
          · exact absurd h hnx
          · have h2 : ¬ (1 < x / (n : ℝ)) := by
              rw [lt_div_iff₀ hnR]; simp; linarith
            have h2' : ¬ ((n : ℝ) < x) := by linarith
            simp [h2', h2]
        have hind_eq : ind n = f n * (if (n : ℝ) < x then (1 : ℂ) else 0) := by
          by_cases h : (n : ℝ) ≤ x
          · have hlt : (n : ℝ) < x := lt_of_le_of_ne h hnx
            simp only [ind]
            rw [if_pos h, if_pos hlt, mul_one]
          · have hnot : ¬ (n : ℝ) < x := fun h' => h (le_of_lt h')
            simp only [ind]
            rw [if_neg h, if_neg hnot, mul_zero]
        have hz1 : x / (n : ℝ) ≠ 1 := by
          intro h
          apply hnx
          rw [div_eq_one_iff_eq (ne_of_gt hnR)] at h
          exact h.symm
        have hdev := perronStep_dev_of_pos σ T (x / (n : ℝ)) hσ hT1 hzpos hz1
        have hdiff : ‖(if (n : ℝ) < x then (1 : ℂ) else 0) - perronStep σ T (x / (n : ℝ))‖ ≤
            (32 / (2 * Real.pi)) * (x / (n : ℝ)) ^ σ *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) := by
          rw [hI, norm_sub_rev]
          exact hdev
        have hzero : (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0) = 0 := if_neg hnx
        rw [hzero, add_zero]
        calc ‖ind n - g n‖
            = ‖f n * ((if (n : ℝ) < x then (1 : ℂ) else 0) -
                perronStep σ T (x / (n : ℝ)))‖ := by
              rw [hind_eq]
              simp only [g, hgdef]
              ring_nf
          _ = ‖f n‖ * ‖(if (n : ℝ) < x then (1 : ℂ) else 0) -
                perronStep σ T (x / (n : ℝ))‖ := norm_mul _ _
          _ ≤ (1 / (n : ℝ)) * ((32 / (2 * Real.pi)) * (x / (n : ℝ)) ^ σ *
                min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) := by
              refine mul_le_mul hfnle hdiff (norm_nonneg _) (by positivity)
          _ = (32 / (2 * Real.pi)) * err n := by
              simp only [err, herrdef]
              ring
  -- summability
  have hsum_ind : Summable ind := by
    have hfin : HasSum ind (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ind n) := by
      apply hasSum_sum_of_ne_finset_zero (s := Finset.Icc 0 ⌊x⌋₊)
      intro n hn
      by_cases h : (n : ℝ) ≤ x
      · have hnfl : n ≤ ⌊x⌋₊ := Nat.le_floor h
        exact absurd (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnfl⟩) hn
      · simp only [ind]
        exact if_neg h
    exact hfin.summable
  have hsum_err : Summable err := by
    have h := (Commons.NumberTheory.Moebius.recip_perron_error_sum_le).choose_spec.2
      x σ T hx hσ hσ1 hT hTx
    simpa only [err, herrdef] using h.1
  have hsum_bdry : Summable (fun n : ℕ =>
      if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0) := by
    have hfin : HasSum (fun n : ℕ => if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0)
        (∑ n ∈ ({⌊x⌋₊} : Finset ℕ),
          (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0)) := by
      apply hasSum_sum_of_ne_finset_zero (s := {⌊x⌋₊})
      intro n hn
      have hnfl : (n : ℝ) ≠ x := by
        intro h
        exact hn (Finset.mem_singleton.mpr (by rw [← h]; simp))
      simp [hnfl]
    exact hfin.summable
  have hsum_rhs : Summable (fun n : ℕ => (32 / (2 * Real.pi)) * err n +
      (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0)) := by
    have h1 : Summable (fun n : ℕ => (32 / (2 * Real.pi)) * err n) :=
      hsum_err.mul_left (32 / (2 * Real.pi))
    exact h1.add hsum_bdry
  have hsum_diff : Summable (fun n : ℕ => ind n - g n) :=
    (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hpt n) hsum_rhs).of_norm
  have hsum_g : Summable g := by
    have h := hsum_ind.sub hsum_diff
    simpa using h
  -- the boundary sum is at most `(3/2)/⌊x⌋₊`
  have hbdry_le : (∑' n : ℕ, (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0)) ≤
      (3 / 2) * (1 / (⌊x⌋₊ : ℝ)) := by
    have hsupport : ∀ n : ℕ, n ∉ ({⌊x⌋₊} : Finset ℕ) →
        (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0) = 0 := by
      intro n hn
      have hnfl : (n : ℝ) ≠ x := by
        intro h
        exact hn (Finset.mem_singleton.mpr (by rw [← h]; simp))
      simp [hnfl]
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := {⌊x⌋₊}) hsupport,
      Finset.sum_singleton]
    split_ifs with h
    · exact le_rfl
    · exact mul_nonneg (by norm_num) (div_nonneg (by norm_num) (Nat.cast_nonneg ⌊x⌋₊))
  calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) - recipPerron x T σ‖
      = ‖(∑' n : ℕ, ind n) - (∑' n : ℕ, g n)‖ := by rw [hindsum, ← hgsum]
      _ = ‖∑' n : ℕ, (ind n - g n)‖ := by rw [Summable.tsum_sub hsum_ind hsum_g]
      _ ≤ ∑' n : ℕ, ‖ind n - g n‖ := norm_tsum_le_tsum_norm hsum_diff.norm
      _ ≤ ∑' n : ℕ, ((32 / (2 * Real.pi)) * err n +
            (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0)) :=
            hasSum_le (fun n => hpt n) hsum_diff.norm.hasSum hsum_rhs.hasSum
      _ = (32 / (2 * Real.pi)) * (∑' n : ℕ, err n) +
            (∑' n : ℕ, (if (n : ℝ) = x then (3 / 2) * (1 / (n : ℝ)) else 0)) := by
            rw [Summable.tsum_add (hsum_err.mul_left _) hsum_bdry, tsum_mul_left]
      _ ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, err n) + (3 / 2) * (1 / (⌊x⌋₊ : ℝ)) := by
            linarith [hbdry_le]

/-! ## 4. The contour-shift bound -/

/-- The integrand `x^s / ζ₁(1+s)` of the reciprocal Perron integral. -/
def recipInt (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s / riemannZeta₁ (1 + s)

/-- `s ↦ x^s/ζ₁(1+s)` is holomorphic on any rectangle on which `ζ(1+·)` does not vanish. -/
lemma recipInt_differentiableOn (x : ℝ) (hx : 0 < x) {z w : ℂ}
    (hrect : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ {s : ℂ | riemannZeta (1 + s) ≠ 0}) :
    DifferentiableOn ℂ (recipInt x) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
  intro s hs
  have hzs : riemannZeta (1 + s) ≠ 0 := hrect hs
  have hz1 : riemannZeta₁ (1 + s) ≠ 0 := by
    by_cases h0 : s = 0
    · subst h0
      rw [show (1 : ℂ) + 0 = 1 by ring, riemannZeta₁_one]
      exact one_ne_zero
    · rw [riemannZeta₁_one_add s h0]
      exact mul_ne_zero h0 hzs
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hnum : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow (f := id) differentiableAt_id (Or.inl hxne)
  have hden : DifferentiableAt ℂ (fun s : ℂ => riemannZeta₁ (1 + s)) s :=
    (differentiable_riemannZeta₁.differentiableAt).comp s (differentiableAt_id.const_add 1)
  exact (hnum.div hden hz1).differentiableWithinAt

/-- The rectangle integral of `x^s/ζ₁(1+s)` vanishes. -/
lemma recipInt_rectInt_eq_zero (x : ℝ) (hx : 0 < x) {z w : ℂ}
    (hrect : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ {s : ℂ | riemannZeta (1 + s) ≠ 0}) :
    Commons.NumberTheory.Zeta.rectInt z w (recipInt x) = 0 := by
  have H := recipInt_differentiableOn x hx hrect
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (recipInt x) z w H
  simpa [Commons.NumberTheory.Zeta.rectInt] using hc

/-- **Contour shift.**  The right-edge integral (which is `2π·recipPerron`) is bounded by
the sum of the three other edge integrals. -/
theorem recipPerron_le_edges (x T σ δ : ℝ) (hx : 0 < x) (hT : 0 < T) (hσ : 0 < σ) (hδ : 0 < δ)
    (hrect : (Set.uIcc (-δ) σ ×ℂ Set.uIcc (-T) T) ⊆ {s : ℂ | riemannZeta (1 + s) ≠ 0}) :
    ‖recipPerron x T σ‖ ≤ (1 / (2 * Real.pi)) *
      (‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ +
       ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ +
       ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖) := by
  set z : ℂ := ((-δ : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I with hzdef
  set w : ℂ := ((σ : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I with hwdef
  have hzre' : z.re = -δ := by simp [z]
  have hzim' : z.im = -T := by simp [z]
  have hwre' : w.re = σ := by simp [w]
  have hwim' : w.im = T := by simp [w]
  have hrect' : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ {s : ℂ | riemannZeta (1 + s) ≠ 0} := by
    rw [hzre', hwre', hzim', hwim']; exact hrect
  have h0 := recipInt_rectInt_eq_zero x hx hrect'
  rw [Commons.NumberTheory.Zeta.rectInt, hzre', hwre', hzim', hwim'] at h0
  have hI : Complex.I • (∫ (t : ℝ) in -T..T,
        recipInt x (((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) -
      (∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)) +
      Complex.I • (∫ (t : ℝ) in -T..T,
        recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)) := by
    linear_combination h0
  have hnorm : ‖∫ (t : ℝ) in -T..T, recipInt x (((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ +
      ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ +
      ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have hI' : ‖Complex.I • (∫ (t : ℝ) in -T..T,
          recipInt x (((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ =
        ‖∫ (t : ℝ) in -T..T, recipInt x (((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    rw [← hI', hI]
    calc ‖(∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) -
            (∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)) +
            Complex.I • (∫ (t : ℝ) in -T..T,
              recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ ‖(∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) -
              (∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I))‖ +
            ‖Complex.I • (∫ (t : ℝ) in -T..T,
              recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I))‖ := norm_add_le _ _
      _ ≤ (‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ +
            ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖) +
          ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ := by
            refine add_le_add ?_ ?_
            · exact norm_sub_le _ _
            · rw [norm_smul, Complex.norm_I, one_mul]
      _ = _ := by ring
  have hrec : recipPerron x T σ =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ (t : ℝ) in -T..T, recipInt x (((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    simp only [recipPerron, recipInt]
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show ((σ : ℂ) + Complex.I * (t : ℂ)) = ((σ : ℂ) + (t : ℂ) * Complex.I) by ring]
  rw [hrec, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hle : ‖∫ (t : ℝ) in -T..T, recipInt x (((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ +
      ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ +
      ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    linarith [hnorm]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-! ## 5. Auxiliary bounds: `1/ζ` near the axis and absorption of log-powers -/

/-- `(1/ζ)` is bounded on a fixed strip `1-ε ≤ Re s ≤ 1`, `|Im s| ≤ 3`, away from `s = 1`
(where `ζ` has a pole).  Compactness, using that `ζ` has no zeros there. -/
lemma zeta_inv_bound_near_axis :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ σ t : ℝ, 1 - ε ≤ σ → σ ≤ 1 → |t| ≤ 3 → σ ≠ 1 →
      ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤ K := by
  obtain ⟨ε₀, hε₀pos, hZF⟩ := Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
  have hεpos : 0 < min ε₀ (1 / 2 : ℝ) := lt_min hε₀pos (by norm_num)
  let ε : ℝ := min ε₀ (1 / 2 : ℝ)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  let S : Set ℂ := {s : ℂ | 1 - ε ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ 3}
  have hS : IsCompact S := by
    have himg : S = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
        (Set.Icc (1 - ε) 1 ×ˢ Set.Icc (-3 : ℝ) 3) := by
      ext s
      constructor
      · intro hs
        refine ⟨(s.re, s.im), ⟨⟨hs.1, hs.2.1⟩, (abs_le.mp hs.2.2)⟩, ?_⟩
        simpa using (Complex.re_add_im s).symm
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨hp1, hp2⟩ := hp
        refine ⟨?_, ?_, ?_⟩
        · simpa using hp1.1
        · simpa using hp1.2
        · rw [show ((↑p.1 + ↑p.2 * Complex.I : ℂ)).im = p.2 by simp]
          exact abs_le.mpr hp2
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hz1 : ∀ s ∈ S, riemannZeta₁ s ≠ 0 := by
    intro s hs
    obtain ⟨hs1, hs2, hs3⟩ := hs
    have h1 : 1 - ε₀ ≤ s.re := by
      have : ε ≤ ε₀ := min_le_left _ _; linarith
    have h3 : |s.im| ≤ 4 := by linarith
    have hzf := hZF s.im s.re h3 h1 (by linarith : s.re ≤ 2)
    have heq : ((s.re : ℂ) + Complex.I * (s.im : ℂ)) = s := by
      rw [show Complex.I * (s.im : ℂ) = (s.im : ℂ) * Complex.I by ring, Complex.re_add_im]
    rw [heq] at hzf
    by_cases hs_eq : s = 1
    · subst hs_eq
      rw [riemannZeta₁_one]
      exact one_ne_zero
    · have hsr : riemannZeta (1 + (s - 1)) ≠ 0 := by
        rwa [show 1 + (s - 1) = s by ring]
      rw [show s = 1 + (s - 1) by ring, riemannZeta₁_one_add (s - 1) (by
        intro h
        exact hs_eq (by linear_combination h))]
      exact mul_ne_zero (sub_ne_zero.mpr hs_eq) hsr
  have hcont : ContinuousOn (fun s : ℂ => (s - 1) / riemannZeta₁ s) S := by
    refine ContinuousOn.div ?_ ?_ hz1
    · exact ((continuous_id.sub continuous_const)).continuousOn
    · exact differentiable_riemannZeta₁.continuous.continuousOn
  obtain ⟨K₀, hK₀⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨ε, max K₀ 1, hεpos, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro σ t hσ hσ1 ht hσne
  have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hσ
    · simpa using hσ1
    · rw [abs_le] at ht ⊢
      simpa using ht
  have hbound := hK₀ _ hmem
  have hs1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    apply hσne
    have := congrArg Complex.re h
    simpa using this
  have hkey : (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹ =
      (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) / riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    have h := riemannZeta_eq_inv_sub_mul (s := (σ : ℂ) + (t : ℂ) * Complex.I) hs1
    rw [h]
    field_simp
  rw [hkey]
  exact le_trans hbound (le_max_left _ _)

/-- Absorb polynomial factors of `log x` into `exp(-c√(log x))`, uniformly over `x ≥ 2`. -/
lemma poly_mul_exp_neg_sqrtLog_le_uniform (c : ℝ) (hc : 0 < c) (k : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ x : ℝ, 2 ≤ x →
      K * (Real.log x) ^ k * Real.exp (-c * Real.sqrt (Real.log x)) ≤
        C' * Real.exp (-c' * Real.sqrt (Real.log x)) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le c hc k K hK)
  set y₀ : ℝ := max x₀ 2 with hy₀def
  have hy₀2 : (2 : ℝ) ≤ y₀ := le_max_right _ _
  have hlogy₀ : 0 ≤ Real.log y₀ := Real.log_nonneg (by linarith)
  set B : ℝ := K * (Real.log y₀) ^ k * Real.exp ((c / 2) * Real.sqrt (Real.log y₀)) with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  refine ⟨c / 2, max 1 B, by linarith, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx2
  have hCe : (1 : ℝ) ≤ max 1 B := le_max_left _ _
  have hCB : B ≤ max 1 B := le_max_right _ _
  by_cases h : y₀ ≤ x
  · have h1 := hx₀ x (le_trans (le_max_left _ _) h)
    calc K * (Real.log x) ^ k * Real.exp (-c * Real.sqrt (Real.log x))
        ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := h1
      _ = Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * 1 := by ring
      _ ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * max 1 B :=
            mul_le_mul_of_nonneg_left hCe (Real.exp_nonneg _)
      _ = max 1 B * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by ring
  · push Not at h
    have hlogxnn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlogx : Real.log x ≤ Real.log y₀ := Real.log_le_log (by linarith) h.le
    have hpow : (Real.log x) ^ k ≤ (Real.log y₀) ^ k := pow_le_pow_left₀ hlogxnn hlogx k
    have hexp1 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
      nlinarith
    have hLHS : K * (Real.log x) ^ k * Real.exp (-c * Real.sqrt (Real.log x)) ≤
        K * (Real.log y₀) ^ k := by
      calc K * (Real.log x) ^ k * Real.exp (-c * Real.sqrt (Real.log x))
          ≤ K * (Real.log x) ^ k * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = K * (Real.log x) ^ k := by ring
        _ ≤ K * (Real.log y₀) ^ k := mul_le_mul_of_nonneg_left hpow hK
    have hsq : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log y₀) := Real.sqrt_le_sqrt hlogx
    have hexpcancel : Real.exp ((c / 2) * Real.sqrt (Real.log y₀)) *
        Real.exp (-(c / 2) * Real.sqrt (Real.log y₀)) = 1 := by
      rw [← Real.exp_add]
      rw [show (c / 2) * Real.sqrt (Real.log y₀) + -(c / 2) * Real.sqrt (Real.log y₀) = 0 by ring,
        Real.exp_zero]
    have hRHS : K * (Real.log y₀) ^ k ≤ max 1 B * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
      calc K * (Real.log y₀) ^ k
          = K * (Real.log y₀) ^ k *
              (Real.exp ((c / 2) * Real.sqrt (Real.log y₀)) *
                Real.exp (-(c / 2) * Real.sqrt (Real.log y₀))) := by rw [hexpcancel, mul_one]
        _ = B * Real.exp (-(c / 2) * Real.sqrt (Real.log y₀)) := by rw [hB]; ring
        _ ≤ max 1 B * Real.exp (-(c / 2) * Real.sqrt (Real.log y₀)) :=
              mul_le_mul_of_nonneg_right hCB (Real.exp_nonneg _)
        _ ≤ max 1 B * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    linarith [hLHS, hRHS]

/-! ## 6. Pointwise bounds for the Perron integrand on the edges -/

/-- Perturbed horizontal edges: for `u ∈ [-δ, σ]` and `|sgn| = T ≥ 3`, the integrand
is bounded by `x^σ (1/T) (Czf (log (T+2))^Czf)`. -/
lemma recipInt_horiz_le (x T σ δ czf Czf sgn u : ℝ) (hx1 : 1 ≤ x)
    (hT : 3 ≤ T) (hδ : 0 < δ) (hδle : δ ≤ czf / Real.log (T + 2)) (hczf : 0 < czf)
    (hCzf : 0 ≤ Czf)
    (hZF : ∀ σ' t : ℝ, 3 ≤ |t| → 1 - czf / Real.log (|t| + 2) ≤ σ' → σ' ≤ 2 →
      1 / ‖riemannZeta ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Czf * (Real.log (|t| + 2)) ^ Czf)
    (hsgn : |sgn| = T) (hu1 : -δ ≤ u) (hu2 : u ≤ σ) (hσ1 : σ ≤ 1) :
    ‖recipInt x ((u : ℂ) + (sgn : ℂ) * Complex.I)‖ ≤
      x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf) := by
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hsre : ((u : ℂ) + (sgn : ℂ) * Complex.I).re = u := by simp
  have hsim : ((u : ℂ) + (sgn : ℂ) * Complex.I).im = sgn := by simp
  have hsne : ((u : ℂ) + (sgn : ℂ) * Complex.I) ≠ 0 := by
    intro hh
    have h := congrArg Complex.im hh
    rw [hsim] at h
    simp at h
    rw [h, abs_zero] at hsgn
    linarith
  have hnorm1 : ‖(x : ℂ) ^ ((u : ℂ) + (sgn : ℂ) * Complex.I)‖ = x ^ u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hsre]
  have hz1 : riemannZeta₁ (1 + ((u : ℂ) + (sgn : ℂ) * Complex.I)) =
      ((u : ℂ) + (sgn : ℂ) * Complex.I) *
        riemannZeta (1 + ((u : ℂ) + (sgn : ℂ) * Complex.I)) :=
    riemannZeta₁_one_add _ hsne
  have hsge : T ≤ ‖((u : ℂ) + (sgn : ℂ) * Complex.I)‖ := by
    have h := Complex.abs_im_le_norm ((u : ℂ) + (sgn : ℂ) * Complex.I)
    rw [hsim, hsgn] at h
    exact h
  have hsgepos : 0 < ‖((u : ℂ) + (sgn : ℂ) * Complex.I)‖ := lt_of_lt_of_le hTpos hsge
  have harg : 1 + ((u : ℂ) + (sgn : ℂ) * Complex.I) =
      ((1 + u : ℝ) : ℂ) + (sgn : ℂ) * Complex.I := by push_cast; ring
  have hzf : 1 / ‖riemannZeta (1 + ((u : ℂ) + (sgn : ℂ) * Complex.I))‖ ≤
      Czf * (Real.log (T + 2)) ^ Czf := by
    have h1 : 3 ≤ |sgn| := by rw [hsgn]; exact hT
    have hlog : Real.log (|sgn| + 2) = Real.log (T + 2) := by rw [hsgn]
    have h2 : 1 - czf / Real.log (|sgn| + 2) ≤ 1 + u := by
      rw [hlog]
      linarith [hδle, hu1]
    have h3 : 1 + u ≤ 2 := by linarith
    have h4 := hZF (1 + u) sgn h1 h2 h3
    rw [hlog] at h4
    rw [harg]
    exact h4
  calc ‖recipInt x ((u : ℂ) + (sgn : ℂ) * Complex.I)‖
      = x ^ u / ‖riemannZeta₁ (1 + ((u : ℂ) + (sgn : ℂ) * Complex.I))‖ := by
        rw [recipInt, norm_div, hnorm1]
    _ = x ^ u * ((‖((u : ℂ) + (sgn : ℂ) * Complex.I)‖ *
          ‖riemannZeta (1 + ((u : ℂ) + (sgn : ℂ) * Complex.I))‖))⁻¹ := by
        rw [hz1, norm_mul, div_eq_mul_inv]
    _ ≤ x ^ u * ((T * ‖riemannZeta (1 + ((u : ℂ) + (sgn : ℂ) * Complex.I))‖))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hxpos.le u)
        rw [mul_inv, mul_inv]
        exact mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ hsgepos hTpos).mpr hsge) (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ x ^ σ * ((T * ‖riemannZeta (1 + ((u : ℂ) + (sgn : ℂ) * Complex.I))‖))⁻¹ := by
        refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 hu2) ?_
        exact inv_nonneg.mpr (mul_nonneg (le_of_lt hTpos) (norm_nonneg _))
    _ = (x ^ σ / T) * (1 / ‖riemannZeta (1 + ((u : ℂ) + (sgn : ℂ) * Complex.I))‖) := by
        rw [mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ ≤ (x ^ σ / T) * (Czf * (Real.log (T + 2)) ^ Czf) :=
        mul_le_mul_of_nonneg_left hzf (by positivity)
    _ = x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf) := by ring

/-- The left edge: for `|t| ≤ T`, the integrand at `-δ + i t` is bounded by
`x^{-δ} δ^{-1} (Kb + Czf (log (T+2))^Czf)`. -/
lemma recipInt_vert_le (x T δ εb Kb czf Czf t : ℝ) (hx1 : 1 ≤ x)
    (hT : 3 ≤ T) (hδ : 0 < δ) (hδle : δ ≤ czf / Real.log (T + 2)) (hδb : δ ≤ εb)
    (hczf : 0 < czf) (hCzf : 0 ≤ Czf) (hKb : 0 ≤ Kb) (hεb : 0 < εb)
    (hNAb : ∀ σ' t' : ℝ, 1 - εb ≤ σ' → σ' ≤ 1 → |t'| ≤ 3 → σ' ≠ 1 →
      ‖(riemannZeta ((σ' : ℂ) + (t' : ℂ) * Complex.I))⁻¹‖ ≤ Kb)
    (hZF : ∀ σ' t' : ℝ, 3 ≤ |t'| → 1 - czf / Real.log (|t'| + 2) ≤ σ' → σ' ≤ 2 →
      1 / ‖riemannZeta ((σ' : ℂ) + (t' : ℂ) * Complex.I)‖ ≤ Czf * (Real.log (|t'| + 2)) ^ Czf)
    (ht : |t| ≤ T) :
    ‖recipInt x (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      x ^ (-δ) * (1 / δ) * (Kb + Czf * (Real.log (T + 2)) ^ Czf) := by
  have hxpos : 0 < x := by linarith
  have hsre : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = -δ := by simp
  have hsim : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have hsne : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro hh
    have h := congrArg Complex.re hh
    rw [hsre] at h
    simp at h
    linarith
  have hnorm1 : ‖(x : ℂ) ^ (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = x ^ (-δ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hsre]
  have hz1 : riemannZeta₁ (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        riemannZeta (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    riemannZeta₁_one_add _ hsne
  have hsge : δ ≤ ‖(((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have h := Complex.abs_re_le_norm (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    rw [hsre, abs_neg, abs_of_nonneg (le_of_lt hδ)] at h
    exact h
  have hsgepos : 0 < ‖(((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := lt_of_lt_of_le hδ hsge
  have harg : 1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      ((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
  have hzf : 1 / ‖riemannZeta (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      Kb + Czf * (Real.log (T + 2)) ^ Czf := by
    rw [harg]
    by_cases ht3 : |t| ≤ 3
    · have hna := hNAb (1 - δ) t (by linarith) (by linarith) ht3 (by linarith)
      rw [one_div, ← norm_inv]
      exact le_trans hna (le_add_of_nonneg_right
        (mul_nonneg hCzf (Real.rpow_nonneg (Real.log_nonneg (by linarith)) Czf)))
    · push Not at ht3
      have hlog : Real.log (|t| + 2) ≤ Real.log (T + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hl : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith)
      have h3 : czf / Real.log (T + 2) ≤ czf / Real.log (|t| + 2) :=
        div_le_div_of_nonneg_left (le_of_lt hczf) hl hlog
      have h2 : 1 - czf / Real.log (|t| + 2) ≤ 1 - δ := by linarith [hδle]
      have h4 := hZF (1 - δ) t (by linarith) h2 (by linarith)
      have h5 : Czf * (Real.log (|t| + 2)) ^ Czf ≤ Czf * (Real.log (T + 2)) ^ Czf :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (le_of_lt hl) hlog hCzf) hCzf
      have h4' : ‖riemannZeta (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖⁻¹ ≤
          Czf * (Real.log (|t| + 2)) ^ Czf := by
        simpa only [one_div] using h4
      rw [one_div]
      exact le_trans h4' (le_trans h5 (le_add_of_nonneg_left hKb))
  calc ‖recipInt x (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      = x ^ (-δ) / ‖riemannZeta₁ (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
        rw [recipInt, norm_div, hnorm1]
    _ = x ^ (-δ) * ((‖(((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
          ‖riemannZeta (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖))⁻¹ := by
        rw [hz1, norm_mul, div_eq_mul_inv]
    _ ≤ x ^ (-δ) * ((δ * ‖riemannZeta (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hxpos.le _)
        rw [mul_inv, mul_inv]
        exact mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ hsgepos hδ).mpr hsge) (inv_nonneg.mpr (norm_nonneg _))
    _ = (x ^ (-δ) / δ) * (1 / ‖riemannZeta (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖) := by
        rw [mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ ≤ (x ^ (-δ) / δ) * (Kb + Czf * (Real.log (T + 2)) ^ Czf) :=
        mul_le_mul_of_nonneg_left hzf (by positivity)
    _ = x ^ (-δ) * (1 / δ) * (Kb + Czf * (Real.log (T + 2)) ^ Czf) := by ring

/-! ## 6. The main theorem -/

/-- **The reciprocal Möbius sum has de la Vallée Poussin decay:**
`Σ_{n ≤ x} μ(n)/n = O(exp(-c√(log x)))`. -/
theorem moebius_recip_sum_exp_decay :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)|
        ≤ C * Real.exp (-(c * Real.sqrt (Real.log x))) := by
  -- ---------- numerical data ----------
  obtain ⟨czf, Czf, hczf_pos, hCzf_pos, hZF⟩ := Commons.NumberTheory.Zeta.zeta_inv_le_logPow_zeroFree
  obtain ⟨czf2, Czf2, hczf2_pos, _, hZFnv, _⟩ :=
    Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
  obtain ⟨ε0, hε0_pos, hNAnv⟩ := Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
  obtain ⟨εb, Kb, hεb_pos, hKb_pos, hNAb⟩ := zeta_inv_bound_near_axis
  obtain ⟨Cm, hCm_pos, hm⟩ := Commons.NumberTheory.Moebius.recip_perron_error_sum_le
  set c₀ : ℝ := min czf czf2 with hc0def
  have hc0pos : 0 < c₀ := lt_min hczf_pos hczf2_pos
  have hc0zf : c₀ ≤ czf := min_le_left _ _
  have hc02 : c₀ ≤ czf2 := min_le_right _ _
  set θ : ℝ := min (min (c₀ / 4) (1 / 2)) (Real.sqrt (c₀ / 3)) with hθdef
  have hθle1 : θ ≤ c₀ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hθle2 : θ ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hθle3 : θ ≤ Real.sqrt (c₀ / 3) := min_le_right _ _
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact lt_min (lt_min (by linarith) (by norm_num)) (Real.sqrt_pos_of_pos (by linarith))
  have hθsq : 3 * θ ^ 2 ≤ c₀ := by
    have h2 : θ ^ 2 ≤ c₀ / 3 := by
      calc θ ^ 2 ≤ (Real.sqrt (c₀ / 3)) ^ 2 := pow_le_pow_left₀ (le_of_lt hθpos) hθle3 2
        _ = c₀ / 3 := Real.sq_sqrt (by linarith)
    linarith
  have hθneed : θ / 2 ≤ c₀ / (2 * θ) - θ := by
    have h1 : 3 * θ ^ 2 ≤ c₀ := hθsq
    have h2 : 0 < 2 * θ := by linarith
    have h3 : 3 * θ ^ 2 / (2 * θ) ≤ c₀ / (2 * θ) := div_le_div_of_nonneg_right h1 (le_of_lt h2)
    have h4 : 3 * θ ^ 2 / (2 * θ) = 3 * θ / 2 := by field_simp
    rw [h4] at h3
    linarith
  set L1 : ℝ := max 8 (max (4 / θ ^ 2) (max ((2 * c₀ / (ε0 * θ)) ^ 2) ((2 * c₀ / (εb * θ)) ^ 2)))
    with hL1def
  have hL1ge8 : 8 ≤ L1 := le_max_left _ _
  have hL1geθ : 4 / θ ^ 2 ≤ L1 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hL1geε0 : (2 * c₀ / (ε0 * θ)) ^ 2 ≤ L1 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hL1geεb : (2 * c₀ / (εb * θ)) ^ 2 ≤ L1 :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  set x₁ : ℝ := Real.exp L1 with hx1def
  have hx1pos : 0 < x₁ := by rw [hx1def]; exact Real.exp_pos _
  have hx1ge4 : 4 ≤ x₁ := by
    rw [hx1def]
    have hlog4 : Real.log 4 ≤ L1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
      linarith
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp L1 := Real.exp_le_exp.mpr hlog4
  -- ---------- constants ----------
  set Ae : ℝ := (32 / (2 * Real.pi)) * Cm * (Real.exp 1 + 1) + 3 with hAedef
  have hAe_pos : 0 < Ae := by
    rw [hAedef]
    have : (0 : ℝ) < Real.exp 1 + 1 := by positivity
    positivity
  set C1 : ℝ := (1 + ε0) * 3 * Czf with hC1def
  have hC1_pos : 0 < C1 := by rw [hC1def]; positivity
  set C2 : ℝ := (4 * θ / c₀) * Kb + (4 * θ / c₀) * Czf with hC2def
  have hC2_nonneg : 0 ≤ C2 := by rw [hC2def]; positivity
  set Cb : ℝ := (1 / (2 * Real.pi)) * (2 * C1 + C2) with hCbdef
  have hCb_pos : 0 < Cb := by rw [hCbdef]; positivity
  set kb : ℕ := Nat.ceil Czf + 2 with hkbdef
  have hkbge1 : 1 ≤ kb := by rw [hkbdef]; omega
  have hkbgeC : Nat.ceil Czf ≤ kb := by rw [hkbdef]; omega
  have hkbgeC1 : Nat.ceil Czf + 1 ≤ kb := by rw [hkbdef]; omega
  set k0 : ℕ := max 1 kb with hk0def
  have hk0ge1 : 1 ≤ k0 := le_max_left _ _
  have hk0geb : kb ≤ k0 := le_max_right _ _
  set K0 : ℝ := (2 * (Ae + Cb)) * 2 ^ k0 with hK0def
  have hK0_pos : 0 < K0 := by rw [hK0def]; positivity
  have hK0_nonneg : 0 ≤ K0 := le_of_lt hK0_pos
  -- ---------- the large-`x` bound ----------
  have hlarge : ∀ x : ℝ, x₁ ≤ x →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ))‖ ≤
        K0 * (Real.log x) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt (Real.log x)) := by
    intro x hx
    set L : ℝ := Real.log x with hLdef
    set T : ℝ := Real.exp (θ * Real.sqrt L) with hTdef
    set σ : ℝ := 1 / L with hσdef
    set δ : ℝ := c₀ / Real.log (T + 3) with hδdef
    have hxpos : (0 : ℝ) < x := by linarith [le_trans hx1ge4 hx]
    have hLge : L1 ≤ L := by
      rw [hLdef]
      exact (Real.le_log_iff_exp_le hxpos).mpr (by rw [← hx1def]; exact hx)
    have hLge8 : 8 ≤ L := le_trans hL1ge8 hLge
    have hLpos : 0 < L := by linarith
    have hLge1 : 1 ≤ L := by linarith
    have hLnonneg : 0 ≤ L := le_of_lt hLpos
    have hsqL : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLnonneg
    have hsqL' : Real.sqrt L * Real.sqrt L = L := by rw [← sq]; exact hsqL
    have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos_of_pos hLpos
    have hsqrtLge2 : 2 ≤ Real.sqrt L := by
      have h16 : (2 : ℝ) ^ 2 ≤ L := by norm_num; linarith
      calc (2 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt L := Real.sqrt_le_sqrt h16
    have hθsqrtL : 2 ≤ θ * Real.sqrt L := by
      have h2θ : 2 / θ ≤ Real.sqrt L := by
        have h4 : 4 / θ ^ 2 ≤ L := le_trans hL1geθ hLge
        have h : (2 / θ) ^ 2 ≤ L := by
          rw [show (2 / θ) ^ 2 = 4 / θ ^ 2 by field_simp; ring]; exact h4
        calc 2 / θ = Real.sqrt ((2 / θ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt L := Real.sqrt_le_sqrt h
      have heq : θ * (2 / θ) = 2 := by field_simp
      calc 2 = θ * (2 / θ) := heq.symm
        _ ≤ θ * Real.sqrt L := mul_le_mul_of_nonneg_left h2θ (le_of_lt hθpos)
    have hTpos : 0 < T := by rw [hTdef]; exact Real.exp_pos _
    have hTge3 : 3 ≤ T := by
      rw [hTdef]
      have h3 : (3 : ℝ) ≤ Real.exp 2 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        rw [h2]
        nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
      exact le_trans h3 (Real.exp_le_exp.mpr hθsqrtL)
    have hTle_x : T ≤ x := by
      have h1 : θ ≤ Real.sqrt L := le_trans hθle2 (le_trans (by linarith : (1:ℝ)/2 ≤ 2) hsqrtLge2)
      have h2 : θ * Real.sqrt L ≤ L := by
        calc θ * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
              mul_le_mul_of_nonneg_right h1 (le_of_lt hsqrtL_pos)
          _ = L := hsqL'
      calc T = Real.exp (θ * Real.sqrt L) := hTdef
        _ ≤ Real.exp L := Real.exp_le_exp.mpr h2
        _ = Real.exp (Real.log x) := by rw [hLdef]
        _ = x := Real.exp_log hxpos
    have hσpos : 0 < σ := by rw [hσdef]; positivity
    have hσle1 : σ ≤ 1 := by rw [hσdef, div_le_one hLpos]; linarith
    have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hc0pos (Real.log_pos (by linarith))
    have hlogT3pos : 0 < Real.log (T + 3) := Real.log_pos (by linarith)
    have hlogT3ge : θ * Real.sqrt L ≤ Real.log (T + 3) := by
      have h := Real.log_le_log hTpos (by linarith : T ≤ T + 3)
      rwa [Real.log_exp] at h
    have hlogT3le : Real.log (T + 3) ≤ 2 * (θ * Real.sqrt L) := by
      have hT3 : T + 3 ≤ 2 * T := by linarith
      have hlog2T : Real.log (2 * T) = Real.log 2 + Real.log T :=
        Real.log_mul (by norm_num) hTpos.ne'
      have hlogT : Real.log T = θ * Real.sqrt L := by rw [hTdef, Real.log_exp]
      have hlog2le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      calc Real.log (T + 3) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hT3
        _ = Real.log 2 + Real.log T := hlog2T
        _ ≤ 1 + θ * Real.sqrt L := by rw [hlogT]; linarith
        _ ≤ 2 * (θ * Real.sqrt L) := by nlinarith [hθsqrtL]
    have hθsqrtL_ε0 : 2 * c₀ / ε0 ≤ θ * Real.sqrt L := by
      have h2 : (2 * c₀ / (ε0 * θ)) ^ 2 ≤ L := le_trans hL1geε0 hLge
      have h : 2 * c₀ / (ε0 * θ) ≤ Real.sqrt L := by
        have hx : (0 : ℝ) ≤ 2 * c₀ / (ε0 * θ) :=
          div_nonneg (by positivity) (le_of_lt (mul_pos hε0_pos hθpos))
        calc 2 * c₀ / (ε0 * θ) = Real.sqrt ((2 * c₀ / (ε0 * θ)) ^ 2) := (Real.sqrt_sq hx).symm
          _ ≤ Real.sqrt L := Real.sqrt_le_sqrt h2
      have heq : θ * (2 * c₀ / (ε0 * θ)) = 2 * c₀ / ε0 := by field_simp
      calc 2 * c₀ / ε0 = θ * (2 * c₀ / (ε0 * θ)) := heq.symm
        _ ≤ θ * Real.sqrt L := mul_le_mul_of_nonneg_left h (le_of_lt hθpos)
    have hθsqrtL_εb : 2 * c₀ / εb ≤ θ * Real.sqrt L := by
      have h2 : (2 * c₀ / (εb * θ)) ^ 2 ≤ L := le_trans hL1geεb hLge
      have h : 2 * c₀ / (εb * θ) ≤ Real.sqrt L := by
        have hx : (0 : ℝ) ≤ 2 * c₀ / (εb * θ) :=
          div_nonneg (by positivity) (le_of_lt (mul_pos hεb_pos hθpos))
        calc 2 * c₀ / (εb * θ) = Real.sqrt ((2 * c₀ / (εb * θ)) ^ 2) := (Real.sqrt_sq hx).symm
          _ ≤ Real.sqrt L := Real.sqrt_le_sqrt h2
      have heq : θ * (2 * c₀ / (εb * θ)) = 2 * c₀ / εb := by field_simp
      calc 2 * c₀ / εb = θ * (2 * c₀ / (εb * θ)) := heq.symm
        _ ≤ θ * Real.sqrt L := mul_le_mul_of_nonneg_left h (le_of_lt hθpos)
    have hδ_le_ε0 : δ ≤ ε0 := by
      rw [hδdef, div_le_iff₀ hlogT3pos]
      have h2 : c₀ ≤ ε0 * (θ * Real.sqrt L) := by
        have h3 : ε0 * (2 * c₀ / ε0) ≤ ε0 * (θ * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hθsqrtL_ε0 hε0_pos.le
        rw [mul_div_cancel₀ (2 * c₀) hε0_pos.ne'] at h3
        linarith
      have h4 : ε0 * (θ * Real.sqrt L) ≤ ε0 * Real.log (T + 3) :=
        mul_le_mul_of_nonneg_left hlogT3ge hε0_pos.le
      linarith
    have hδ_le_εb : δ ≤ εb := by
      rw [hδdef, div_le_iff₀ hlogT3pos]
      have h2 : c₀ ≤ εb * (θ * Real.sqrt L) := by
        have h3 : εb * (2 * c₀ / εb) ≤ εb * (θ * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hθsqrtL_εb hεb_pos.le
        rw [mul_div_cancel₀ (2 * c₀) hεb_pos.ne'] at h3
        linarith
      have h4 : εb * (θ * Real.sqrt L) ≤ εb * Real.log (T + 3) :=
        mul_le_mul_of_nonneg_left hlogT3ge hεb_pos.le
      linarith
    have hδ_le_zf : δ ≤ czf / Real.log (T + 2) := by
      have hlogT2pos : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
      have hlog23 : Real.log (T + 2) ≤ Real.log (T + 3) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [hδdef, div_le_div_iff₀ hlogT3pos hlogT2pos]
      have h1 : c₀ * Real.log (T + 2) ≤ czf * Real.log (T + 2) :=
        mul_le_mul_of_nonneg_right hc0zf (le_of_lt hlogT2pos)
      have h2 : czf * Real.log (T + 2) ≤ czf * Real.log (T + 3) :=
        mul_le_mul_of_nonneg_left hlog23 (le_of_lt hczf_pos)
      linarith
    have hδ_le_c2 : δ ≤ czf2 / Real.log (T + 3) := by
      rw [hδdef, div_le_div_iff₀ hlogT3pos hlogT3pos]
      have h1 : c₀ * Real.log (T + 3) ≤ czf2 * Real.log (T + 3) :=
        mul_le_mul_of_nonneg_right hc02 (le_of_lt hlogT3pos)
      linarith
    have hxσ : x ^ σ = Real.exp 1 := by
      rw [hσdef, Real.rpow_def_of_pos hxpos, one_div, ← hLdef, mul_inv_cancel₀ hLpos.ne']
    have hTinv : (1 : ℝ) / T = Real.exp (-θ * Real.sqrt L) := by
      rw [hTdef, one_div, ← Real.exp_neg]
      congr 1
      ring
    have hkbC : (Nat.ceil Czf : ℝ) ≤ (kb : ℝ) := Nat.cast_le.mpr hkbgeC
    have hkbC1 : (Nat.ceil Czf : ℝ) + 1 ≤ (kb : ℝ) := by
      have h : (((Nat.ceil Czf + 1 : ℕ)) : ℝ) ≤ (kb : ℝ) := Nat.cast_le.mpr hkbgeC1
      push_cast at h
      exact h
    -- ---------- the zero-free rectangle ----------
    have hrect : (Set.uIcc (-δ) σ ×ℂ Set.uIcc (-T) T) ⊆ {s : ℂ | riemannZeta (1 + s) ≠ 0} := by
      intro s hs
      rw [Complex.mem_reProdIm] at hs
      obtain ⟨hsre, hsim⟩ := hs
      rw [Set.uIcc_of_le (by linarith : -δ ≤ σ)] at hsre
      rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hsim
      rw [Set.mem_Icc] at hsre hsim
      have hre1 : 1 - ε0 ≤ 1 + s.re := by linarith [hsre.1, hδ_le_ε0]
      have hre2 : 1 + s.re ≤ 2 := by linarith [hsre.2, hσle1]
      have hsimT : |s.im| ≤ T := abs_le.mpr ⟨hsim.1, hsim.2⟩
      have heq : ((1 + s.re : ℝ) : ℂ) + Complex.I * (s.im : ℂ) = 1 + s := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
        · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
      by_cases hcase : |s.im| ≤ 4
      · have h := hNAnv s.im (1 + s.re) hcase hre1 hre2
        rwa [heq] at h
      · push Not at hcase
        have him1 : 1 ≤ |s.im| := by linarith
        have h2 : 1 - czf2 / Real.log (|s.im| + 3) ≤ 1 + s.re := by
          have hlog : Real.log (|s.im| + 3) ≤ Real.log (T + 3) :=
            Real.log_le_log (by linarith) (by linarith)
          have hl : 0 < Real.log (|s.im| + 3) := Real.log_pos (by linarith)
          have h3 : czf2 / Real.log (T + 3) ≤ czf2 / Real.log (|s.im| + 3) :=
            div_le_div_of_nonneg_left hczf2_pos.le hl hlog
          linarith [hδ_le_c2]
        have h := hZFnv s.im him1 (1 + s.re) h2
        rwa [heq] at h
    -- ---------- the truncation error ----------
    have hbound1 : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ)) - recipPerron x T σ‖ ≤
        Ae * (1 + L) * Real.exp (-θ * Real.sqrt L) := by
      have h3x : (3 : ℝ) ≤ x := by linarith
      have hT2 : (2 : ℝ) ≤ T := by linarith
      have hmain := recipPerron_sub_sum_le x T h3x hT2 hTle_x hσpos hσle1
      have hsum := (hm x σ T h3x hσpos hσle1 hT2 hTle_x).2
      have hxσ : x ^ σ = Real.exp 1 := by
        rw [hσdef, Real.rpow_def_of_pos hxpos, one_div, ← hLdef, mul_inv_cancel₀ hLpos.ne']
      have hinvσ : 1 / σ = L := by rw [hσdef]; simp
      have hTinv : (1 : ℝ) / T = Real.exp (-θ * Real.sqrt L) := by
        rw [hTdef, one_div, ← Real.exp_neg]
        congr 1
        ring
      have hexpnn : 0 ≤ Real.exp (-θ * Real.sqrt L) := Real.exp_nonneg _
      have hkey : x ^ σ * (1 + 1 / σ) + 1 ≤ (Real.exp 1 + 1) * (1 + L) := by
        rw [hxσ, hinvσ]
        have h1 : (1 : ℝ) ≤ 1 + L := by linarith
        calc Real.exp 1 * (1 + L) + 1 ≤ Real.exp 1 * (1 + L) + (1 + L) := by linarith
          _ = (Real.exp 1 + 1) * (1 + L) := by ring
      have hE : (∑' n : ℕ, (1 / (n : ℝ)) * (x / (n : ℝ)) ^ σ *
            min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤
          Cm * (Real.exp 1 + 1) * (1 + L) * Real.exp (-θ * Real.sqrt L) := by
        calc (∑' n : ℕ, (1 / (n : ℝ)) * (x / (n : ℝ)) ^ σ *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|)))
            ≤ Cm * (x ^ σ * (1 + 1 / σ) + 1) / T := hsum
          _ = Cm * (x ^ σ * (1 + 1 / σ) + 1) * (1 / T) := by ring
          _ = Cm * (x ^ σ * (1 + 1 / σ) + 1) * Real.exp (-θ * Real.sqrt L) := by rw [hTinv]
          _ ≤ Cm * ((Real.exp 1 + 1) * (1 + L)) * Real.exp (-θ * Real.sqrt L) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hCm_pos.le) hexpnn
          _ = Cm * (Real.exp 1 + 1) * (1 + L) * Real.exp (-θ * Real.sqrt L) := by ring
      have hfloorpos : 0 < ((⌊x⌋₊ : ℕ) : ℝ) := by
        have h2 : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith : ((1:ℕ):ℝ) ≤ x)
        have h3 : (0 : ℕ) < ⌊x⌋₊ := by omega
        exact_mod_cast h3
      have hfloor : x / 2 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
        have h := Nat.lt_floor_add_one x
        push_cast
        linarith
      have hbdry : (3 / 2) * (1 / ((⌊x⌋₊ : ℕ) : ℝ)) ≤ 3 * Real.exp (-θ * Real.sqrt L) := by
        have h1 : (1 : ℝ) / ((⌊x⌋₊ : ℕ) : ℝ) ≤ 2 / x := by
          rw [div_le_div_iff₀ hfloorpos hxpos]
          have hh : x / 2 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := hfloor
          linarith
        have h2 : (2 : ℝ) / x = 2 * Real.exp (-L) := by
          have hxL : x = Real.exp L := by rw [hLdef]; exact (Real.exp_log hxpos).symm
          rw [hxL, div_eq_mul_inv, ← Real.exp_neg]
        have h3 : Real.exp (-L) ≤ Real.exp (-θ * Real.sqrt L) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : θ ≤ Real.sqrt L :=
            le_trans hθle2 (le_trans (by linarith : (1:ℝ)/2 ≤ 2) hsqrtLge2)
          have h2 : θ * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hsqrtL_pos)
          rw [hsqL'] at h2
          linarith
        linarith
      have h32 : 0 ≤ 32 / (2 * Real.pi) := by positivity
      have hfirst : (32 / (2 * Real.pi)) * (∑' n : ℕ, (1 / (n : ℝ)) * (x / (n : ℝ)) ^ σ *
            min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤
          (32 / (2 * Real.pi)) * (Cm * (Real.exp 1 + 1) * (1 + L) *
            Real.exp (-θ * Real.sqrt L)) :=
        mul_le_mul_of_nonneg_left hE h32
      calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ)) -
              recipPerron x T σ‖
          ≤ (32 / (2 * Real.pi)) * (∑' n : ℕ, (1 / (n : ℝ)) * (x / (n : ℝ)) ^ σ *
              min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) +
            (3 / 2) * (1 / ((⌊x⌋₊ : ℕ) : ℝ)) := hmain
        _ ≤ (32 / (2 * Real.pi)) * (Cm * (Real.exp 1 + 1) * (1 + L) *
              Real.exp (-θ * Real.sqrt L)) + 3 * Real.exp (-θ * Real.sqrt L) := by
              linarith [hfirst, hbdry]
        _ ≤ Ae * (1 + L) * Real.exp (-θ * Real.sqrt L) := by
              have hstep : (32 / (2 * Real.pi)) * (Cm * (Real.exp 1 + 1) * (1 + L) *
                    Real.exp (-θ * Real.sqrt L)) + 3 * Real.exp (-θ * Real.sqrt L) =
                  ((32 / (2 * Real.pi)) * Cm * (Real.exp 1 + 1) * (1 + L) + 3) *
                    Real.exp (-θ * Real.sqrt L) := by ring
              rw [hstep]
              have hle : (32 / (2 * Real.pi)) * Cm * (Real.exp 1 + 1) * (1 + L) + 3 ≤
                  Ae * (1 + L) := by
                rw [hAedef]
                have heq : ((32 / (2 * Real.pi)) * Cm * (Real.exp 1 + 1) + 3) * (1 + L) =
                    (32 / (2 * Real.pi)) * Cm * (Real.exp 1 + 1) * (1 + L) + 3 * (1 + L) := by
                  ring
                rw [heq]
                linarith
              calc ((32 / (2 * Real.pi)) * Cm * (Real.exp 1 + 1) * (1 + L) + 3) *
                    Real.exp (-θ * Real.sqrt L)
                  ≤ (Ae * (1 + L)) * Real.exp (-θ * Real.sqrt L) :=
                    mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
                _ = Ae * (1 + L) * Real.exp (-θ * Real.sqrt L) := by ring
    -- ---------- the Perron integral ----------
    have hpowC : (Real.log (T + 2)) ^ Czf ≤ (1 + L) ^ (Nat.ceil Czf : ℝ) := by
      have hlogT2nonneg : 0 ≤ Real.log (T + 2) := le_of_lt (Real.log_pos (by linarith))
      have hlogT2le : Real.log (T + 2) ≤ 2 * (θ * Real.sqrt L) :=
        le_trans (Real.log_le_log (by linarith) (by linarith : T + 2 ≤ T + 3)) hlogT3le
      have h1 : (Real.log (T + 2)) ^ Czf ≤ (2 * (θ * Real.sqrt L)) ^ Czf :=
        Real.rpow_le_rpow hlogT2nonneg hlogT2le hCzf_pos.le
      have h2 : (2 * (θ * Real.sqrt L)) ^ Czf ≤ (1 + L) ^ (Nat.ceil Czf : ℝ) := by
        rw [show 2 * (θ * Real.sqrt L) = (2 * θ) * Real.sqrt L by ring,
          Real.mul_rpow (by positivity) (Real.sqrt_nonneg L)]
        have h2θ1 : (2 * θ) ^ Czf ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) hCzf_pos.le
        have hsq : (Real.sqrt L) ^ Czf ≤ (1 + L) ^ (Nat.ceil Czf : ℝ) := by
          have hbase : Real.sqrt L ≤ 1 + L := by
            have h1 : (1 : ℝ) ≤ Real.sqrt L := by linarith
            have h2 : Real.sqrt L ≤ Real.sqrt L * Real.sqrt L := by
              have hh := mul_le_mul_of_nonneg_left h1 (le_of_lt hsqrtL_pos)
              rwa [mul_one] at hh
            rw [hsqL'] at h2
            linarith
          have hb1 : (Real.sqrt L) ^ Czf ≤ (1 + L) ^ Czf :=
            Real.rpow_le_rpow (Real.sqrt_nonneg L) hbase hCzf_pos.le
          have hb2 : (1 + L) ^ Czf ≤ (1 + L) ^ (Nat.ceil Czf : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil Czf)
          linarith
        calc (2 * θ) ^ Czf * (Real.sqrt L) ^ Czf ≤ 1 * (1 + L) ^ (Nat.ceil Czf : ℝ) :=
              mul_le_mul h2θ1 hsq (Real.rpow_nonneg (Real.sqrt_nonneg L) _) (by norm_num)
          _ = (1 + L) ^ (Nat.ceil Czf : ℝ) := one_mul _
      exact h1.trans h2
    have hpowCmono : (1 + L) ^ (Nat.ceil Czf : ℝ) ≤ (1 + L) ^ kb := by
      rw [← Real.rpow_natCast (1 + L) kb]
      exact Real.rpow_le_rpow_of_exponent_le (x := 1 + L) (by linarith) hkbC
    have hpowCkb : (1 + L) ^ (Nat.ceil Czf : ℝ) * (1 + L) ≤ (1 + L) ^ kb := by
      have h1 : (1 + L) ^ ((Nat.ceil Czf : ℝ) + 1) = (1 + L) ^ (Nat.ceil Czf : ℝ) * (1 + L) := by
        rw [Real.rpow_add (by linarith : (0:ℝ) < 1 + L), Real.rpow_one]
      rw [← h1]
      have h2 : (1 + L) ^ ((Nat.ceil Czf : ℝ) + 1) ≤ (1 + L) ^ (kb : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hkbC1
      rwa [Real.rpow_natCast] at h2
    have hE2 : Real.exp (-θ * Real.sqrt L) ≤ Real.exp (-(θ / 2) * Real.sqrt L) := by
      refine Real.exp_le_exp.mpr ?_
      have h3 : 0 ≤ θ * Real.sqrt L := mul_nonneg hθpos.le hsqrtL_pos.le
      linarith
    have hE2pos : 0 ≤ Real.exp (-(θ / 2) * Real.sqrt L) := Real.exp_nonneg _
    have hFpos : 0 < Real.exp (-(θ / 2) * Real.sqrt L) := Real.exp_pos _
    have hbound2 : ‖recipPerron x T σ‖ ≤ Cb * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by
      have hrec := recipPerron_le_edges x T σ δ hxpos hTpos hσpos hδpos hrect
      have hlogT2pos : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
      have hargTneg : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_nonneg (le_of_lt hTpos)]
      have hargT : |(T : ℝ)| = T := abs_of_nonneg (le_of_lt hTpos)
      have hCzfnn : (0 : ℝ) ≤ Czf := le_of_lt hCzf_pos
      have hCzpos : 0 < Czf := hCzf_pos
      -- the three edge estimates
      have hA : ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ ≤
          (σ + δ) * (x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf)) := by
        have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := -δ) (b := σ)
          (C := x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf))
          (f := fun u : ℝ => recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I))
          (fun u hu => recipInt_horiz_le x T σ δ czf Czf (-T) u (by linarith) hTge3 hδpos
            hδ_le_zf hczf_pos hCzfnn hZF hargTneg
            (by have h := hu.1; rw [min_eq_left (by linarith : -δ ≤ σ)] at h; exact le_of_lt h)
            (by have h := hu.2; rw [max_eq_right (by linarith : -δ ≤ σ)] at h; exact h) hσle1)
        calc ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖
            ≤ x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf) * |σ - (-δ)| := hmain
          _ = (σ + δ) * (x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf)) := by
              rw [abs_of_nonneg (by linarith)]; ring
      have hB : ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤
          (σ + δ) * (x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf)) := by
        have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := -δ) (b := σ)
          (C := x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf))
          (f := fun u : ℝ => recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
          (fun u hu => recipInt_horiz_le x T σ δ czf Czf T u (by linarith) hTge3 hδpos
            hδ_le_zf hczf_pos hCzfnn hZF hargT
            (by have h := hu.1; rw [min_eq_left (by linarith : -δ ≤ σ)] at h; exact le_of_lt h)
            (by have h := hu.2; rw [max_eq_right (by linarith : -δ ≤ σ)] at h; exact h) hσle1)
        calc ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
            ≤ x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf) * |σ - (-δ)| := hmain
          _ = (σ + δ) * (x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf)) := by
              rw [abs_of_nonneg (by linarith)]; ring
      have hD : ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          (T + T) * (x ^ (-δ) * (1 / δ) * (Kb + Czf * (Real.log (T + 2)) ^ Czf)) := by
        have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
          (C := x ^ (-δ) * (1 / δ) * (Kb + Czf * (Real.log (T + 2)) ^ Czf))
          (f := fun t : ℝ => recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I))
          (fun t ht => recipInt_vert_le x T δ εb Kb czf Czf t (by linarith) hTge3 hδpos hδ_le_zf
            hδ_le_εb hczf_pos hCzfnn hKb_pos.le hεb_pos hNAb hZF
            (abs_le.mpr ⟨by
                have h := ht.1; rw [min_eq_left (by linarith : -T ≤ T)] at h; exact le_of_lt h,
              by have h := ht.2; rw [max_eq_right (by linarith : -T ≤ T)] at h; exact h⟩))
        calc ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ x ^ (-δ) * (1 / δ) * (Kb + Czf * (Real.log (T + 2)) ^ Czf) * |T - (-T)| := hmain
          _ = (T + T) * (x ^ (-δ) * (1 / δ) * (Kb + Czf * (Real.log (T + 2)) ^ Czf)) := by
              rw [abs_of_nonneg (by linarith)]; ring
      -- reduce each to the shape `C1/C2 * (1+L)^kb * exp(-(θ/2)√L)`
      have hA' : ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ ≤
          C1 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by
        have h1 : σ + δ ≤ 1 + ε0 := by linarith [hσle1, hδ_le_ε0]
        have h2 : x ^ σ ≤ 3 := by rw [hxσ]; exact le_of_lt Real.exp_one_lt_three
        have h3 : (1 : ℝ) / T ≤ Real.exp (-θ * Real.sqrt L) := by rw [hTinv]
        have hA2 : (1 / T) * (Real.log (T + 2)) ^ Czf ≤
            Real.exp (-θ * Real.sqrt L) * (1 + L) ^ kb :=
          mul_le_mul h3 (hpowC.trans hpowCmono)
            (Real.rpow_nonneg (le_of_lt hlogT2pos) _) (Real.exp_nonneg _)
        calc ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖
            ≤ (σ + δ) * (x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf)) := hA
          _ = (σ + δ) * x ^ σ * (1 / T) * Czf * (Real.log (T + 2)) ^ Czf := by ring
          _ ≤ (1 + ε0) * 3 * Real.exp (-θ * Real.sqrt L) * Czf * (1 + L) ^ kb := by
              have hA1 : (σ + δ) * x ^ σ ≤ (1 + ε0) * 3 :=
                mul_le_mul h1 h2 (Real.rpow_nonneg hxpos.le σ) (by linarith)
              have hA3 : (σ + δ) * x ^ σ * (1 / T) * Czf * (Real.log (T + 2)) ^ Czf =
                  ((σ + δ) * x ^ σ * Czf) * ((1 / T) * (Real.log (T + 2)) ^ Czf) := by ring
              rw [hA3]
              calc ((σ + δ) * x ^ σ * Czf) * ((1 / T) * (Real.log (T + 2)) ^ Czf)
                  ≤ ((1 + ε0) * 3 * Czf) * (Real.exp (-θ * Real.sqrt L) * (1 + L) ^ kb) :=
                    mul_le_mul (mul_le_mul hA1 le_rfl hCzf_pos.le (by linarith)) hA2
                      (by positivity) (by positivity)
                _ = (1 + ε0) * 3 * Real.exp (-θ * Real.sqrt L) * Czf * (1 + L) ^ kb := by ring
          _ ≤ (1 + ε0) * 3 * Real.exp (-(θ / 2) * Real.sqrt L) * Czf * (1 + L) ^ kb := by
              have hnn : 0 ≤ (1 + ε0) * 3 * Czf * (1 + L) ^ kb := by positivity
              have hq := mul_le_mul_of_nonneg_left hE2 hnn
              calc (1 + ε0) * 3 * Real.exp (-θ * Real.sqrt L) * Czf * (1 + L) ^ kb
                  = ((1 + ε0) * 3 * Czf * (1 + L) ^ kb) * Real.exp (-θ * Real.sqrt L) := by ring
                _ ≤ ((1 + ε0) * 3 * Czf * (1 + L) ^ kb) * Real.exp (-(θ / 2) * Real.sqrt L) := hq
                _ = (1 + ε0) * 3 * Real.exp (-(θ / 2) * Real.sqrt L) * Czf * (1 + L) ^ kb := by ring
          _ = C1 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by rw [hC1def]; ring
      have hB' : ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤
          C1 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by
        have h1 : σ + δ ≤ 1 + ε0 := by linarith [hσle1, hδ_le_ε0]
        have h2 : x ^ σ ≤ 3 := by rw [hxσ]; exact le_of_lt Real.exp_one_lt_three
        have h3 : (1 : ℝ) / T ≤ Real.exp (-θ * Real.sqrt L) := by rw [hTinv]
        have hA2 : (1 / T) * (Real.log (T + 2)) ^ Czf ≤
            Real.exp (-θ * Real.sqrt L) * (1 + L) ^ kb :=
          mul_le_mul h3 (hpowC.trans hpowCmono)
            (Real.rpow_nonneg (le_of_lt hlogT2pos) _) (Real.exp_nonneg _)
        calc ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
            ≤ (σ + δ) * (x ^ σ * (1 / T) * (Czf * (Real.log (T + 2)) ^ Czf)) := hB
          _ = (σ + δ) * x ^ σ * (1 / T) * Czf * (Real.log (T + 2)) ^ Czf := by ring
          _ ≤ (1 + ε0) * 3 * Real.exp (-θ * Real.sqrt L) * Czf * (1 + L) ^ kb := by
              have hA1 : (σ + δ) * x ^ σ ≤ (1 + ε0) * 3 :=
                mul_le_mul h1 h2 (Real.rpow_nonneg hxpos.le σ) (by linarith)
              have hA3 : (σ + δ) * x ^ σ * (1 / T) * Czf * (Real.log (T + 2)) ^ Czf =
                  ((σ + δ) * x ^ σ * Czf) * ((1 / T) * (Real.log (T + 2)) ^ Czf) := by ring
              rw [hA3]
              calc ((σ + δ) * x ^ σ * Czf) * ((1 / T) * (Real.log (T + 2)) ^ Czf)
                  ≤ ((1 + ε0) * 3 * Czf) * (Real.exp (-θ * Real.sqrt L) * (1 + L) ^ kb) :=
                    mul_le_mul (mul_le_mul hA1 le_rfl hCzf_pos.le (by linarith)) hA2
                      (by positivity) (by positivity)
                _ = (1 + ε0) * 3 * Real.exp (-θ * Real.sqrt L) * Czf * (1 + L) ^ kb := by ring
          _ ≤ (1 + ε0) * 3 * Real.exp (-(θ / 2) * Real.sqrt L) * Czf * (1 + L) ^ kb := by
              have hnn : 0 ≤ (1 + ε0) * 3 * Czf * (1 + L) ^ kb := by positivity
              have hq := mul_le_mul_of_nonneg_left hE2 hnn
              calc (1 + ε0) * 3 * Real.exp (-θ * Real.sqrt L) * Czf * (1 + L) ^ kb
                  = ((1 + ε0) * 3 * Czf * (1 + L) ^ kb) * Real.exp (-θ * Real.sqrt L) := by ring
                _ ≤ ((1 + ε0) * 3 * Czf * (1 + L) ^ kb) * Real.exp (-(θ / 2) * Real.sqrt L) := hq
                _ = (1 + ε0) * 3 * Real.exp (-(θ / 2) * Real.sqrt L) * Czf * (1 + L) ^ kb := by ring
          _ = C1 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by rw [hC1def]; ring
      have hD' : ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C2 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by
        have hT2 : T + T = 2 * Real.exp (θ * Real.sqrt L) := by rw [hTdef]; ring
        have hδge : c₀ / (2 * θ * Real.sqrt L) ≤ δ := by
          rw [hδdef, div_le_div_iff₀ (by positivity) hlogT3pos]
          have h1 : c₀ * Real.log (T + 3) ≤ c₀ * (2 * (θ * Real.sqrt L)) :=
            mul_le_mul_of_nonneg_left hlogT3le (le_of_lt hc0pos)
          linarith
        have hxδ : x ^ (-δ) ≤ Real.exp (-(c₀ / (2 * θ)) * Real.sqrt L) := by
          rw [Real.rpow_def_of_pos hxpos]
          refine Real.exp_le_exp.mpr ?_
          rw [← hLdef]
          have h1 : c₀ / (2 * θ) ≤ δ * Real.sqrt L := by
            have h2 : c₀ / (2 * θ * Real.sqrt L) * Real.sqrt L ≤ δ * Real.sqrt L :=
              mul_le_mul_of_nonneg_right hδge hsqrtL_pos.le
            have h3 : c₀ / (2 * θ * Real.sqrt L) * Real.sqrt L = c₀ / (2 * θ) := by
              field_simp
            rwa [h3] at h2
          have h5 : (c₀ / (2 * θ)) * Real.sqrt L ≤ δ * Real.sqrt L * Real.sqrt L :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hsqrtL_pos)
          have h6 : δ * Real.sqrt L * Real.sqrt L = δ * L := by
            rw [show δ * Real.sqrt L * Real.sqrt L = δ * (Real.sqrt L * Real.sqrt L) by ring,
              hsqL']
          linarith [h5, h6.le, h6.ge]
        have hll : Real.log (T + 3) ≤ 2 * θ * Real.sqrt L := by linarith [hlogT3le]
        have hinvδ : 1 / δ ≤ 2 * θ * Real.sqrt L / c₀ := by
          rw [hδdef, one_div, inv_div]
          exact div_le_div_of_nonneg_right hll (le_of_lt hc0pos)
        have hKg : (Kb + Czf * (Real.log (T + 2)) ^ Czf) ≤
            Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hpowC hCzfnn)
        have hexp1 : Real.exp (-(c₀ / (2 * θ)) * Real.sqrt L) ≤ Real.exp (-(θ / 2) * Real.sqrt L) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : θ / 2 ≤ c₀ / (2 * θ) := by linarith [hθneed]
          have h2 : (θ / 2) * Real.sqrt L ≤ (c₀ / (2 * θ)) * Real.sqrt L :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hsqrtL_pos)
          linarith
        have hexp2 : Real.exp ((θ - c₀ / (2 * θ)) * Real.sqrt L) ≤
            Real.exp (-(θ / 2) * Real.sqrt L) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : θ - c₀ / (2 * θ) ≤ -(θ / 2) := by linarith [hθneed]
          have h2 : (θ - c₀ / (2 * θ)) * Real.sqrt L ≤ (-(θ / 2)) * Real.sqrt L :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hsqrtL_pos)
          linarith
        have hD1 : ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            (2 * Real.exp (θ * Real.sqrt L)) *
              (Real.exp (-(c₀ / (2 * θ)) * Real.sqrt L) * (2 * θ * Real.sqrt L / c₀) *
                (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ))) := by
          refine le_trans hD ?_
          rw [hT2]
          refine mul_le_mul le_rfl ?_ (by positivity) (by positivity)
          refine mul_le_mul ?_ hKg (by positivity) (by positivity)
          exact mul_le_mul hxδ hinvδ (by positivity) (Real.exp_nonneg _)
        have hD2 : (2 * Real.exp (θ * Real.sqrt L)) *
              (Real.exp (-(c₀ / (2 * θ)) * Real.sqrt L) * (2 * θ * Real.sqrt L / c₀) *
                (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ))) =
            (4 * θ * Real.sqrt L / c₀) * Real.exp ((θ - c₀ / (2 * θ)) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) := by
          rw [show (θ - c₀ / (2 * θ)) * Real.sqrt L =
            θ * Real.sqrt L + (-(c₀ / (2 * θ)) * Real.sqrt L) by ring, Real.exp_add]
          ring
        have hD3 : (4 * θ * Real.sqrt L / c₀) *
              Real.exp ((θ - c₀ / (2 * θ)) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) ≤
            (4 * θ * Real.sqrt L / c₀) * Real.exp (-(θ / 2) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) := by
          have hcoef : 0 ≤ 4 * θ * Real.sqrt L / c₀ := by positivity
          have hcoef2 : 0 ≤ Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp2 hcoef) hcoef2
        have hsL : Real.sqrt L ≤ 1 + L := by
          have hh1 : (1 : ℝ) ≤ Real.sqrt L := by linarith
          have hh2 : Real.sqrt L ≤ Real.sqrt L * Real.sqrt L := by
            have hh := mul_le_mul_of_nonneg_left hh1 (le_of_lt hsqrtL_pos)
            rwa [mul_one] at hh
          rw [hsqL'] at hh2
          linarith
        have hD4 : (4 * θ * Real.sqrt L / c₀) * Real.exp (-(θ / 2) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) ≤
            (4 * θ / c₀) * (1 + L) * Real.exp (-(θ / 2) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) := by
          have hcoef : (4 * θ / c₀) * Real.sqrt L ≤ (4 * θ / c₀) * (1 + L) :=
            mul_le_mul_of_nonneg_left hsL (by positivity)
          have hcoef2 : 0 ≤ Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ) := by positivity
          calc (4 * θ * Real.sqrt L / c₀) * Real.exp (-(θ / 2) * Real.sqrt L) *
                (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ))
              = ((4 * θ / c₀) * Real.sqrt L) * Real.exp (-(θ / 2) * Real.sqrt L) *
                (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) := by ring
            _ ≤ ((4 * θ / c₀) * (1 + L)) * Real.exp (-(θ / 2) * Real.sqrt L) *
                (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hcoef hE2pos) hcoef2
            _ = (4 * θ / c₀) * (1 + L) * Real.exp (-(θ / 2) * Real.sqrt L) *
                (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) := by ring
        have hD5 : (4 * θ / c₀) * (1 + L) * Real.exp (-(θ / 2) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) ≤
            C2 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by
          have hp : (1 + L) ≤ (1 + L) ^ kb := by
            calc (1 + L) = (1 + L) ^ (1 : ℕ) := (pow_one _).symm
              _ ≤ (1 + L) ^ kb := pow_le_pow_right₀ (by linarith) hkbge1
          have h1 : (1 + L) * Kb ≤ (1 + L) ^ kb * Kb :=
            mul_le_mul_of_nonneg_right hp (le_of_lt hKb_pos)
          have h2 : (1 + L) * (Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) ≤ Czf * (1 + L) ^ kb := by
            have hh := mul_le_mul_of_nonneg_left hpowCkb hCzf_pos.le
            calc (1 + L) * (Czf * (1 + L) ^ (Nat.ceil Czf : ℝ))
                = Czf * ((1 + L) ^ (Nat.ceil Czf : ℝ) * (1 + L)) := by ring
              _ ≤ Czf * (1 + L) ^ kb := hh
          have hinner : (1 + L) * Kb + (1 + L) * (Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) ≤
              (Kb + Czf) * (1 + L) ^ kb := by
            have hsum : (1 + L) * Kb + (1 + L) * (Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) ≤
                (1 + L) ^ kb * Kb + Czf * (1 + L) ^ kb := add_le_add h1 h2
            calc (1 + L) * Kb + (1 + L) * (Czf * (1 + L) ^ (Nat.ceil Czf : ℝ))
                ≤ (1 + L) ^ kb * Kb + Czf * (1 + L) ^ kb := hsum
              _ = (Kb + Czf) * (1 + L) ^ kb := by ring
          calc (4 * θ / c₀) * (1 + L) * Real.exp (-(θ / 2) * Real.sqrt L) *
                (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ))
              = (4 * θ / c₀) * Real.exp (-(θ / 2) * Real.sqrt L) *
                ((1 + L) * Kb + (1 + L) * (Czf * (1 + L) ^ (Nat.ceil Czf : ℝ))) := by ring
            _ ≤ (4 * θ / c₀) * Real.exp (-(θ / 2) * Real.sqrt L) * ((Kb + Czf) * (1 + L) ^ kb) :=
                mul_le_mul_of_nonneg_left hinner (by positivity)
            _ = C2 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by rw [hC2def]; ring
        calc ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ (2 * Real.exp (θ * Real.sqrt L)) *
              (Real.exp (-(c₀ / (2 * θ)) * Real.sqrt L) * (2 * θ * Real.sqrt L / c₀) *
                (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ))) := hD1
          _ = (4 * θ * Real.sqrt L / c₀) * Real.exp ((θ - c₀ / (2 * θ)) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) := hD2
          _ ≤ (4 * θ * Real.sqrt L / c₀) * Real.exp (-(θ / 2) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) := hD3
          _ ≤ (4 * θ / c₀) * (1 + L) * Real.exp (-(θ / 2) * Real.sqrt L) *
              (Kb + Czf * (1 + L) ^ (Nat.ceil Czf : ℝ)) := hD4
          _ ≤ C2 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := hD5
      -- combine the three edge bounds
      have hsum2 : ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ +
          ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ +
          ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          (2 * C1 + C2) * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by
        have h2C : 2 * C1 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) +
            C2 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) =
            (2 * C1 + C2) * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by ring
        have h1 : ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ +
            ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤
            2 * C1 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by
          have : ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ +
              ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤
              C1 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) +
              C1 * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := add_le_add hA' hB'
          linarith
        linarith [h1, hD', h2C]
      calc ‖recipPerron x T σ‖
          ≤ (1 / (2 * Real.pi)) *
            (‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)‖ +
             ‖∫ (u : ℝ) in -δ..σ, recipInt x ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ +
             ‖∫ (t : ℝ) in -T..T, recipInt x ((((-δ : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖) := hrec
        _ ≤ (1 / (2 * Real.pi)) *
              ((2 * C1 + C2) * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L)) :=
            mul_le_mul_of_nonneg_left hsum2 (by positivity)
        _ = Cb * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) := by rw [hCbdef]; ring
    -- ---------- combine ----------
    have hcomb : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ))‖ ≤
        (2 * (Ae + Cb)) * (1 + L) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt L) := by
      have h1 : Real.exp (-θ * Real.sqrt L) ≤ Real.exp (-(θ / 2) * Real.sqrt L) := hE2
      have h2 : (1 + L) ≤ (1 + L) ^ k0 := by
        calc (1 + L) = (1 + L) ^ (1 : ℕ) := (pow_one _).symm
          _ ≤ (1 + L) ^ k0 := pow_le_pow_right₀ (by linarith) hk0ge1
      have hp : (1 + L) ^ kb ≤ (1 + L) ^ k0 := pow_le_pow_right₀ (by linarith) hk0geb
      have hA : Ae * (1 + L) ≤ (Ae + Cb) * (1 + L) ^ k0 := by
        have hAeL : Ae * (1 + L) ≤ (Ae + Cb) * (1 + L) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        calc Ae * (1 + L) ≤ (Ae + Cb) * (1 + L) := hAeL
          _ ≤ (Ae + Cb) * (1 + L) ^ k0 := mul_le_mul_of_nonneg_left h2 (by positivity)
      have hB : Cb * (1 + L) ^ kb ≤ (Ae + Cb) * (1 + L) ^ k0 := by
        have hCbL : Cb ≤ Ae + Cb := by linarith [hAe_pos]
        exact mul_le_mul hCbL hp (by positivity) (by positivity)
      have htri : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ))‖ ≤
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ)) -
              recipPerron x T σ‖ + ‖recipPerron x T σ‖ := by
        calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ))‖
            = ‖((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ)) -
                recipPerron x T σ) + recipPerron x T σ‖ := by rw [sub_add_cancel]
          _ ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ)) -
                recipPerron x T σ‖ + ‖recipPerron x T σ‖ := norm_add_le _ _
      calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ))‖
          ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ)) -
              recipPerron x T σ‖ + ‖recipPerron x T σ‖ := htri
        _ ≤ Ae * (1 + L) * Real.exp (-θ * Real.sqrt L) +
              Cb * (1 + L) ^ kb * Real.exp (-(θ / 2) * Real.sqrt L) :=
              add_le_add hbound1 hbound2
        _ ≤ (Ae + Cb) * (1 + L) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt L) +
              (Ae + Cb) * (1 + L) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt L) :=
              add_le_add
                (mul_le_mul_of_nonneg_right (hA.trans (le_refl _)) hE2pos |> fun h => by
                  calc Ae * (1 + L) * Real.exp (-θ * Real.sqrt L)
                      ≤ (Ae + Cb) * (1 + L) ^ k0 * Real.exp (-θ * Real.sqrt L) :=
                        mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
                    _ ≤ (Ae + Cb) * (1 + L) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt L) :=
                        mul_le_mul_of_nonneg_left h1 (by positivity))
                (mul_le_mul_of_nonneg_right hB hE2pos)
        _ = (2 * (Ae + Cb)) * (1 + L) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt L) := by ring
    calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ))‖
        ≤ (2 * (Ae + Cb)) * (1 + L) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt L) := hcomb
      _ ≤ (2 * (Ae + Cb)) * (2 * L) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt L) := by
            have h1L : (1 + L) ≤ 2 * L := by linarith
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h1L k0) (by positivity))
              (Real.exp_nonneg _)
      _ = K0 * L ^ k0 * Real.exp (-(θ / 2) * Real.sqrt L) := by
            rw [hK0def, mul_pow]; ring
      _ = K0 * (Real.log x) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt (Real.log x)) := by rw [hLdef]
  -- ---------- absorption ----------
  obtain ⟨c', C', hc'pos, hC'pos, habs⟩ :=
    poly_mul_exp_neg_sqrtLog_le_uniform (θ / 2) (by positivity) k0 K0 hK0_nonneg
  refine ⟨c', max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))), hc'pos, ?_, ?_⟩
  · have h1 : (0 : ℝ) < x₁ * Real.exp (c' * Real.sqrt (Real.log x₁)) := by positivity
    exact lt_of_lt_of_le hC'pos (le_max_left _ _)
  · intro x hx2
    by_cases h : x₁ ≤ x
    · have h1 := hlarge x h
      have h2 := habs x hx2
      have h3 : C' * Real.exp (-c' * Real.sqrt (Real.log x)) ≤
          max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))) *
            Real.exp (-c' * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
      have hcast : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ)) =
          (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.ofReal_div]
      have hfin : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤
          max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))) *
            Real.exp (-(c' * Real.sqrt (Real.log x))) := by
        rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hcast]
        calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) : ℂ))‖
            ≤ K0 * (Real.log x) ^ k0 * Real.exp (-(θ / 2) * Real.sqrt (Real.log x)) := h1
          _ ≤ C' * Real.exp (-c' * Real.sqrt (Real.log x)) := h2
          _ ≤ max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))) *
                Real.exp (-c' * Real.sqrt (Real.log x)) := h3
          _ = max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))) *
                Real.exp (-(c' * Real.sqrt (Real.log x))) := by
                congr 1
                congr 1
                ring
      exact hfin
    · push Not at h
      -- small `x`
      have hx2' : (2 : ℝ) ≤ x := hx2
      have hS : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ x₁ := by
        have h1 : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| := by
          rw [← Real.norm_eq_abs]
          refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
          exact Finset.sum_congr rfl fun n _ => by rw [Real.norm_eq_abs]
        have h2 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hn).1
          have h1' := Commons.NumberTheory.Moebius.moebius_abs_le_one n
          rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ))]
          rw [div_le_one (by linarith : (0 : ℝ) < (n : ℝ))]
          linarith [h1', hn1]
        calc |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)|
            ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| := h1
          _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := h2
          _ = ((⌊x⌋₊ : ℕ) : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
              simp
          _ ≤ x₁ := by
              have := Nat.floor_le (by linarith : (0 : ℝ) ≤ x)
              linarith
      have hle : Real.exp (-(c' * Real.sqrt (Real.log x₁))) ≤
          Real.exp (-(c' * Real.sqrt (Real.log x))) := by
        refine Real.exp_le_exp.mpr ?_
        have hlog : Real.log x ≤ Real.log x₁ := Real.log_le_log (by linarith : (0:ℝ) < x) h.le
        have hh : c' * Real.sqrt (Real.log x) ≤ c' * Real.sqrt (Real.log x₁) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog) (le_of_lt hc'pos)
        linarith
      have hexpc : Real.exp (c' * Real.sqrt (Real.log x₁)) *
          Real.exp (-(c' * Real.sqrt (Real.log x₁))) = 1 := by
        rw [← Real.exp_add]
        rw [show c' * Real.sqrt (Real.log x₁) + -(c' * Real.sqrt (Real.log x₁)) = 0 by ring,
          Real.exp_zero]
      have hkey : x₁ ≤ max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))) *
          Real.exp (-(c' * Real.sqrt (Real.log x))) := by
        have h1e : (1 : ℝ) ≤ Real.exp (c' * Real.sqrt (Real.log x₁)) :=
          Real.one_le_exp (by positivity)
        have h2e : x₁ ≤ x₁ * Real.exp (c' * Real.sqrt (Real.log x₁)) := by
          have hh := mul_le_mul_of_nonneg_left h1e hx1pos.le
          rwa [mul_one] at hh
        have h3e : x₁ * Real.exp (c' * Real.sqrt (Real.log x₁)) ≤
            max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))) := le_max_right _ _
        calc x₁ = x₁ * Real.exp (c' * Real.sqrt (Real.log x₁)) *
              Real.exp (-(c' * Real.sqrt (Real.log x₁))) := by
              rw [mul_assoc, hexpc, mul_one]
          _ ≤ max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))) *
              Real.exp (-(c' * Real.sqrt (Real.log x₁))) :=
              mul_le_mul_of_nonneg_right h3e (Real.exp_nonneg _)
          _ ≤ max C' (x₁ * Real.exp (c' * Real.sqrt (Real.log x₁))) *
              Real.exp (-(c' * Real.sqrt (Real.log x))) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
      linarith [hS, hkey]

end

end Commons.NumberTheory.Moebius
