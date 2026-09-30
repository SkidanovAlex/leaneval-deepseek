import Mathlib
import Submission.Commons.Analysis.Fourier.perron_kernel_sigma_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Real Set Complex Filter intervalIntegral MeasureTheory
open scoped Topology Real

namespace Commons.Analysis.Fourier

/-! # Explicit-32 uniform bound for the σ-shifted truncated Perron kernel deviation -/

lemma pskBound32 (σ T α : ℝ) (hσ1 : 1 ≤ σ) (hT : 1 ≤ T) (hα : α ≠ 0) :
    ‖pskInt σ T α - (if 0 < α then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0)‖
      ≤ 32 * min 1 (1 / (T * |α|)) := by
  have hσ : 0 < σ := lt_of_lt_of_le zero_lt_one hσ1
  change ‖pskInt σ T α - (if 0 < α then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0)‖
      ≤ 32 * min 1 (1 / (T * |α|))
  let V : ℂ := if 0 < α then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0
  have hconv : Tendsto (fun R : ℝ => pskInt σ R α) atTop (𝓝 V) := by
    simpa [V, pskInt, pskKern] using (perronKernelSigma_tendsto σ α hσ hα)
  have hδpos : 0 < T * |α| := mul_pos (lt_of_lt_of_le zero_lt_one hT) (abs_pos.mpr hα)
  by_cases hδle : T * |α| ≤ 1
  · have hmin : min 1 (1 / (T * |α|)) = 1 := by
      rw [min_eq_left]
      rw [one_le_div₀ hδpos]
      exact hδle
    rw [hmin]
    have hreg : ‖pskInt σ T α‖ ≤ Real.pi + 2 := by
      have hb : ‖pskInt σ T α‖ ≤ Real.pi + 2 * |α| * T := by
        simpa [pskInt, pskKern] using (perronKernelSigma_regionBound σ T α hσ (le_trans zero_le_one hT))
      have hbt : 2 * |α| * T ≤ 2 := by nlinarith
      nlinarith
    have hVnorm : ‖V‖ ≤ 2 * Real.pi := by
      simpa [V] using psk_value_norm σ α hσ
    have hmain : ‖pskInt σ T α - V‖ ≤ 32 := by
      calc
        ‖pskInt σ T α - V‖ ≤ ‖pskInt σ T α‖ + ‖V‖ := norm_sub_le _ _
        _ ≤ (Real.pi + 2) + 2 * Real.pi := add_le_add hreg hVnorm
        _ ≤ 32 := by nlinarith [Real.pi_lt_four]
    simpa using hmain
  · have hδgt1 : 1 < T * |α| := lt_of_not_ge hδle
    have hmin : min 1 (1 / (T * |α|)) = 1 / (T * |α|) := by
      rw [min_eq_right]
      rw [div_le_one₀ hδpos]
      exact le_of_lt hδgt1
    rw [hmin]
    have htail : ∀ R : ℝ, T ≤ R → ‖pskInt σ R α - pskInt σ T α‖ ≤ 6 / (|α| * T) := by
      intro R hR
      exact psk_tail_bound σ T R α hσ hα hT hR
    have hmain : ‖pskInt σ T α - V‖ ≤ 6 / (|α| * T) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hconvε : ∀ᶠ R in atTop, ‖pskInt σ R α - V‖ < ε := by
        have hh := (Metric.tendsto_nhds.mp hconv) ε hε
        simpa [dist_eq_norm] using hh
      rcases eventually_atTop.1 hconvε with ⟨R0, hR0⟩
      let R1 := max T R0
      have hTR1 : T ≤ R1 := le_max_left _ _
      have hR0R1 : R0 ≤ R1 := le_max_right _ _
      have hεR : ‖pskInt σ R1 α - V‖ ≤ ε := (hR0 R1 hR0R1).le
      have htri : ‖pskInt σ T α - V‖ ≤ ‖pskInt σ T α - pskInt σ R1 α‖ + ‖pskInt σ R1 α - V‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle (pskInt σ T α) (pskInt σ R1 α) V
      calc
        ‖pskInt σ T α - V‖ ≤ ‖pskInt σ T α - pskInt σ R1 α‖ + ‖pskInt σ R1 α - V‖ := htri
        _ ≤ 6 / (|α| * T) + ε := add_le_add
            (by rw [norm_sub_rev]; exact htail R1 hTR1) hεR
    have hmain' : ‖pskInt σ T α - V‖ ≤ 6 / (T * |α|) := by
      simpa [mul_comm] using hmain
    have hcmp : 6 / (T * |α|) ≤ 32 * (1 / (T * |α|)) := by
      rw [div_eq_mul_inv]
      rw [one_div]
      exact mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 32)
        (by positivity : 0 ≤ (T * |α|)⁻¹)
    simpa [V] using hmain'.trans hcmp

/-! # Pointwise integrand identity -/

lemma perronStep_integrand_eq (σ z t : ℝ) (hz : 0 < z) :
    Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ)))
        / ((σ : ℂ) + Complex.I * (t : ℂ))
      = ((z ^ σ : ℝ) : ℂ) * (pskKern σ (Real.log z) t) := by
  unfold pskKern
  rw [← Complex.ofReal_log hz.le]
  set lz : ℝ := Real.log z
  have hprod : ((σ : ℂ) + I * (t : ℂ)) * (lz : ℂ)
      = ((σ * lz : ℝ) : ℂ) + I * ((t * lz : ℝ) : ℂ) := by
    calc
      ((σ : ℂ) + I * (t : ℂ)) * (lz : ℂ)
          = (σ : ℂ) * (lz : ℂ) + (I * (t : ℂ)) * (lz : ℂ) := by ring
      _ = (↑(σ * lz) : ℂ) + I * ((t : ℂ) * (lz : ℂ)) := by
            rw [← Complex.ofReal_mul, mul_assoc]
      _ = (↑(σ * lz) : ℂ) + I * (↑(t * lz) : ℂ) := by
            congr 2
            rw [← Complex.ofReal_mul]
  have h2 : I * ((t * lz : ℝ) : ℂ) = I * ((lz : ℂ) * (t : ℂ)) := by
    rw [Complex.ofReal_mul]
    congr 1
    rw [mul_comm]
  have hzpow' : ((z ^ σ : ℝ) : ℂ) = (Real.exp (σ * lz) : ℂ) := by
    have h1 : z ^ σ = Real.exp (Real.log z * σ) := Real.rpow_def_of_pos hz σ
    calc
      ((z ^ σ : ℝ) : ℂ) = (Real.exp (Real.log z * σ) : ℂ) := by rw [h1]
      _ = (Real.exp (σ * lz) : ℂ) := by
        congr 1
        congr 1
        ring
  calc
    cexp ((↑σ + I * ↑t) * ↑lz) / (↑σ + I * ↑t)
        = cexp (↑(σ * lz) + I * ↑(t * lz)) / (↑σ + I * ↑t) := by rw [hprod]
    _ = cexp (↑(σ * lz)) * cexp (I * ↑(t * lz)) / (↑σ + I * ↑t) := by rw [Complex.exp_add]
    _ = (Real.exp (σ * lz) : ℂ) * cexp (I * ↑(t * lz)) / (↑σ + I * ↑t) := by
          rw [← Complex.ofReal_exp (σ * lz)]
    _ = ((z ^ σ : ℝ) : ℂ) * cexp (I * ↑(t * lz)) / (↑σ + I * ↑t) := by rw [hzpow']
    _ = ((z ^ σ : ℝ) : ℂ) * cexp (I * ((lz : ℂ) * (t : ℂ))) / (↑σ + I * ↑t) := by
          rw [h2]
    _ = ((z ^ σ : ℝ) : ℂ) * (cexp (I * ((lz : ℂ) * (t : ℂ))) / (↑σ + I * ↑t)) := by ring

/-! # The Perron step deviation bound -/

theorem perronStep_deviation (σ T z : ℝ) (hσ : 1 ≤ σ) (hT : 1 ≤ T) (hz : 0 < z)
    (hz1 : z ≠ 1) :
    ‖(1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
          Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ)))
            / ((σ : ℂ) + Complex.I * (t : ℂ)))
        - (if 1 < z then (1 : ℂ) else 0)‖
      ≤ (32 / (2 * Real.pi)) * (z ^ σ) * min 1 (1 / (T * |Real.log z|)) := by
  have hα : Real.log z ≠ 0 := by
    intro h0
    apply hz1
    have hzexp : Real.exp (Real.log z) = z := Real.exp_log hz
    calc
      z = Real.exp (Real.log z) := hzexp.symm
      _ = 1 := by rw [h0]; norm_num
  have hb32 : ‖pskInt σ T (Real.log z)
        - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
      ≤ 32 * min 1 (1 / (T * |Real.log z|)) := by
    exact pskBound32 σ T (Real.log z) hσ hT hα
  have hJ : (∫ (t : ℝ) in -T..T,
        Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ)))
          / ((σ : ℂ) + Complex.I * (t : ℂ)))
      = ((z ^ σ : ℝ) : ℂ) * pskInt σ T (Real.log z) := by
    have hfun : (fun t : ℝ =>
          Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ)))
            / ((σ : ℂ) + Complex.I * (t : ℂ)))
        = fun t : ℝ => ((z ^ σ : ℝ) : ℂ) * pskKern σ (Real.log z) t := by
      funext t
      exact perronStep_integrand_eq σ z t hz
    rw [hfun]
    rw [intervalIntegral.integral_const_mul]
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
          ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) * (2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))))
              = (((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) * (2 * ↑Real.pi)) * cexp (-((σ : ℂ) * ↑(Real.log z))) := by ring
          _ = ((↑((z ^ σ / (2 * Real.pi)) * (2 * Real.pi)) : ℂ)) * cexp (-((σ : ℂ) * ↑(Real.log z))) := by
                have h2 : (2 : ℂ) * ↑Real.pi = (↑(2 * Real.pi) : ℂ) := by norm_num
                rw [h2]
                rw [← Complex.ofReal_mul]
          _ = ((z ^ σ : ℝ) : ℂ) * cexp (-((σ : ℂ) * ↑(Real.log z))) := by
                congr 1
                congr 1
                field_simp
          _ = ((z ^ σ : ℝ) : ℂ) * (Real.exp (-(σ * Real.log z)) : ℂ) := by
                have harg : -(((σ : ℂ) * ↑(Real.log z))) = (↑(-(σ * Real.log z)) : ℂ) := by
                  rw [← Complex.ofReal_mul]
                  norm_num
                rw [harg]
                rw [← Complex.ofReal_exp]
          _ = 1 := by
                rw [← Complex.ofReal_mul]
                rw [hreal]
                norm_num
      rw [hRHS]
    · have hneg : ¬ 1 < z := by
        intro hzgt1
        exact hpos ((Real.log_pos_iff hz.le).mpr hzgt1)
      rw [if_neg hneg, if_neg hpos]
      simp
  -- content equality: (1/2π)·J − W = ↑(z^σ/(2π))·(S − V)
  have hbase : (1 / (2 * Real.pi)) * ((↑(z ^ σ : ℝ) : ℂ) * pskInt σ T (Real.log z))
        - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
            (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)
      = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
          (pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)) := by
    calc
      (1 / (2 * Real.pi)) * ((↑(z ^ σ : ℝ) : ℂ) * pskInt σ T (Real.log z))
          - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
              (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)
          = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((↑(z ^ σ : ℝ) : ℂ) * pskInt σ T (Real.log z))
              - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
                simp
          _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) * (↑(z ^ σ : ℝ) : ℂ)) * pskInt σ T (Real.log z)
              - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
                ring
          _ = (↑((1 / (2 * Real.pi)) * z ^ σ) : ℂ) * pskInt σ T (Real.log z)
              - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
                rw [← Complex.ofReal_mul]
          _ = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) * pskInt σ T (Real.log z)
              - ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
                  (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0) := by
                congr 1
                congr 1
                field_simp
          _ = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
              (pskInt σ T (Real.log z)
                - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)) := by
                rw [mul_sub]
  have hcontent : (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
          Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ)))
            / ((σ : ℂ) + Complex.I * (t : ℂ)))
        - (if 1 < z then (1 : ℂ) else 0)
      = ((z ^ σ / (2 * Real.pi) : ℝ) : ℂ) *
          (pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)) := by
    rw [hJ, hW]
    exact hbase
  -- positivity of the scalar
  have hscal_nonneg : 0 ≤ z ^ σ / (2 * Real.pi) := by positivity
  -- ‖c·x‖ = |c|·‖x‖ for the lifted positive real scalar c = z^σ/(2π)
  have hnormfac : ‖(((z ^ σ / (2 * Real.pi) : ℝ) : ℂ)) *
            (pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0))‖
        = (z ^ σ / (2 * Real.pi)) *
            ‖pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖ := by
    calc
      ‖(((z ^ σ / (2 * Real.pi) : ℝ) : ℂ)) *
            (pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0))‖
          = ‖(((z ^ σ / (2 * Real.pi) : ℝ) : ℂ))‖ *
              ‖pskInt σ T (Real.log z)
                - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖ :=
                norm_mul _ _
      _ = |z ^ σ / (2 * Real.pi)| *
            ‖pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖ := by
            rw [show ‖(((z ^ σ / (2 * Real.pi) : ℝ) : ℂ))‖ = |z ^ σ / (2 * Real.pi)| by
              simpa using (RCLike.norm_ofReal (K := ℂ) (z ^ σ / (2 * Real.pi)))]
      _ = (z ^ σ / (2 * Real.pi)) *
            ‖pskInt σ T (Real.log z)
              - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖ := by
            rw [abs_of_nonneg hscal_nonneg]
  have hfin : (z ^ σ / (2 * Real.pi)) * ‖pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
        ≤ (32 / (2 * Real.pi)) * z ^ σ * min 1 (1 / (T * |Real.log z|)) := by
    calc
      (z ^ σ / (2 * Real.pi)) * ‖pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
          ≤ (z ^ σ / (2 * Real.pi)) * (32 * min 1 (1 / (T * |Real.log z|))) := by
            exact mul_le_mul_of_nonneg_left hb32 hscal_nonneg
      _ = (32 / (2 * Real.pi)) * z ^ σ * min 1 (1 / (T * |Real.log z|)) := by ring
  rw [hcontent, hnormfac]
  exact hfin

end Commons.Analysis.Fourier
