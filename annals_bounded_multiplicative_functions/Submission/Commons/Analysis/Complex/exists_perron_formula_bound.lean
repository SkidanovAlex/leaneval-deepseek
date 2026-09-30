import Mathlib
import Submission.Commons.Analysis.Fourier.perronStep_deviation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex MeasureTheory intervalIntegral Filter
open scoped BigOperators Topology

namespace Commons.Analysis.Complex

namespace PerronPos

open Commons.Analysis.Fourier Commons.Analysis.Fourier.PerronSigma

lemma oscV_norm_le_pos (σ t : ℝ) (hσ : σ ≠ 0) (ht : 0 < t) :
    ‖oscV σ t‖ ≤ t⁻¹ := by
  unfold oscV
  rw [norm_inv]
  have hz0 : 0 < ‖((σ : ℂ) + I * (t : ℂ) : ℂ)‖ :=
    norm_pos_iff.mpr (sigma_add_I_ne_zero σ t hσ)
  exact (inv_le_inv₀ hz0 ht).mpr (sigma_add_I_norm_ge σ t ht.le)

lemma oscW_norm_le_pos (α σ t : ℝ) (hσ : σ ≠ 0) (ht : 0 < t) :
    ‖oscW α σ t‖ ≤ (|α| * t)⁻¹ := by
  unfold oscW
  calc
    ‖oscU α t * oscV σ t‖ ≤ ‖oscU α t‖ * ‖oscV σ t‖ := norm_mul_le _ _
    _ = (|α|)⁻¹ * ‖oscV σ t‖ := by rw [oscU_norm]
    _ ≤ (|α|)⁻¹ * t⁻¹ :=
        mul_le_mul_of_nonneg_left (oscV_norm_le_pos σ t hσ ht) (inv_nonneg.mpr (abs_nonneg α))
    _ = (|α| * t)⁻¹ := by rw [← mul_inv]

lemma oscW_norm_bound_pos (α σ t T : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0) (htT : T ≤ t)
    (hT : 0 < T) : ‖oscW α σ t‖ ≤ (|α| * T)⁻¹ := by
  have ht : 0 < t := lt_of_lt_of_le hT htT
  refine le_trans (oscW_norm_le_pos α σ t hσ ht) ?_
  have hle : |α| * T ≤ |α| * t := mul_le_mul_of_nonneg_left htT (abs_nonneg α)
  have hbpos : 0 < |α| * t := mul_pos (abs_pos.mpr hα) ht
  have hapos : 0 < |α| * T := mul_pos (abs_pos.mpr hα) hT
  exact (inv_le_inv₀ hbpos hapos).mpr hle

lemma inv_sigma_add_sq_le_inv_sq_pos (σ t : ℝ) (ht : 0 < t) :
    (σ ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ := by
  have hle : t ^ 2 ≤ σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg σ]
  have hpos1 : 0 < σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg σ, sq_pos_of_pos ht]
  have hpos2 : 0 < t ^ 2 := sq_pos_of_pos ht
  exact (inv_le_inv₀ hpos1 hpos2).mpr hle

lemma integral_inv_sigma_add_sq_le_pos (σ T R : ℝ) (hσ : σ ≠ 0) (hT : 0 < T) (hTR : T ≤ R) :
    (∫ t in T..R, (σ ^ 2 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  have hmono : (∫ t in T..R, (σ ^ 2 + t ^ 2)⁻¹) ≤ ∫ t in T..R, (t ^ 2)⁻¹ := by
    refine intervalIntegral.integral_mono_on hTR ?hf ?hg ?h
    · exact (continuous_inv_sigma_add_sq σ hσ).intervalIntegrable T R
    · exact integrable_inv_sq_Icc T R hT hTR
    · intro x hx
      exact inv_sigma_add_sq_le_inv_sq_pos σ x (lt_of_lt_of_le hT hx.1)
  have hval : (∫ t in T..R, (t ^ 2)⁻¹) = T⁻¹ - R⁻¹ :=
    integral_inv_sq_of_pos T R hT (lt_of_lt_of_le hT hTR)
  rw [hval] at hmono
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hT hTR))
  linarith

lemma oscR_integral_norm_le_pos (α σ T R : ℝ) (hσ : σ ≠ 0) (hT : 0 < T) (hTR : T ≤ R) :
    ‖∫ t in T..R, oscR α σ t‖ ≤ (|α|)⁻¹ * T⁻¹ := by
  calc
    ‖∫ t in T..R, oscR α σ t‖ ≤ ∫ t in T..R, ‖oscR α σ t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hTR
    _ ≤ ∫ t in T..R, (|α|)⁻¹ * (σ ^ 2 + t ^ 2)⁻¹ := by
      exact intervalIntegral.integral_mono_on hTR
        (((cont_oscR α σ hσ).norm).intervalIntegrable T R)
        (((continuous_const.mul (continuous_inv_sigma_add_sq σ hσ))).intervalIntegrable T R)
        (fun x _ => oscR_norm_le α σ x)
    _ = (|α|)⁻¹ * (∫ t in T..R, (σ ^ 2 + t ^ 2)⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (|α|)⁻¹ * T⁻¹ :=
      mul_le_mul_of_nonneg_left (integral_inv_sigma_add_sq_le_pos σ T R hσ hT hTR)
        (inv_nonneg.mpr (abs_nonneg α))

end PerronPos

open Commons.Analysis.Fourier Commons.Analysis.Fourier.PerronSigma

theorem perronKernelSigma_oscTail_pos (σ T R α : ℝ) (hσ : 0 < σ) (hα : α ≠ 0)
    (hT : 0 < T) (hTR : T ≤ R) :
    ‖(∫ (t : ℝ) in T..R, Complex.exp (Complex.I * (↑α * ↑t)) / ((σ : ℂ) + Complex.I * ↑t))‖ ≤
      3 / (|α| * T) := by
  have hσnz : σ ≠ 0 := ne_of_gt hσ
  have hconv : (∫ t in T..R, Complex.exp (Complex.I * (↑α * ↑t)) / ((σ : ℂ) + Complex.I * ↑t))
      = ∫ t in T..R, oscG α σ t := by
    apply intervalIntegral.integral_congr
    intro x hx
    rfl
  rw [hconv]
  have hbound : ‖oscW α σ R - oscW α σ T‖ ≤ 2 * (|α| * T)⁻¹ := by
    calc
      ‖oscW α σ R - oscW α σ T‖ ≤ ‖oscW α σ R‖ + ‖oscW α σ T‖ := norm_sub_le _ _
      _ ≤ 2 * (|α| * T)⁻¹ := by
        have h1 := PerronPos.oscW_norm_bound_pos α σ R T hα hσnz hTR hT
        have h2 := PerronPos.oscW_norm_bound_pos α σ T T hα hσnz le_rfl hT
        nlinarith
  have hint : ‖∫ t in T..R, oscR α σ t‖ ≤ (|α| * T)⁻¹ := by
    have h := PerronPos.oscR_integral_norm_le_pos α σ T R hσnz hT hTR
    rwa [← mul_inv] at h
  have hmain : ‖∫ t in T..R, oscG α σ t‖ ≤ 3 * (|α| * T)⁻¹ := by
    calc
      ‖∫ t in T..R, oscG α σ t‖ = ‖(oscW α σ R - oscW α σ T) - ∫ t in T..R, oscR α σ t‖ := by
        rw [osc_integral_identity α σ T R hα hσnz]
      _ ≤ ‖oscW α σ R - oscW α σ T‖ + ‖∫ t in T..R, oscR α σ t‖ := norm_sub_le _ _
      _ ≤ 2 * (|α| * T)⁻¹ + (|α| * T)⁻¹ := add_le_add hbound hint
      _ = 3 * (|α| * T)⁻¹ := by ring
  rw [div_eq_mul_inv]
  exact hmain

lemma psk_neg_tail_pos (σ T R α : ℝ) (hσ : 0 < σ) (hα : α ≠ 0) (hT : 0 < T) (hTR : T ≤ R) :
    ‖(∫ t in -R..-T, pskKern σ α t)‖ ≤ 3 / (|α| * T) := by
  have hσnz : σ ≠ 0 := ne_of_gt hσ
  have hsub : (∫ t in -R..-T, pskKern σ α t) = ∫ u in T..R, pskKern σ α (-u) := by
    have h1 := intervalIntegral.integral_comp_neg (f := fun u : ℝ => pskKern σ α u) (a := T) (b := R)
    exact h1.symm
  have hconjpt : (fun u : ℝ => pskKern σ α (-u)) = fun u : ℝ => (starRingEnd ℂ) (pskKern σ α u) := by
    funext u
    exact (psk_conj_neg σ α u).symm
  have hfi : IntervalIntegrable (pskKern σ α) volume T R :=
    (psk_continuous σ α hσnz).intervalIntegrable T R
  calc
    ‖(∫ t in -R..-T, pskKern σ α t)‖ = ‖∫ u in T..R, pskKern σ α (-u)‖ := by rw [hsub]
    _ = ‖∫ u in T..R, (starRingEnd ℂ) (pskKern σ α u)‖ := by rw [hconjpt]
    _ = ‖(starRingEnd ℂ) (∫ u in T..R, pskKern σ α u)‖ := by
          rw [psk_conj_integral (pskKern σ α) T R hfi]
    _ = ‖∫ u in T..R, pskKern σ α u‖ := by rw [Complex.norm_conj]
    _ ≤ 3 / (|α| * T) := by
      simpa [pskKern] using (perronKernelSigma_oscTail_pos σ T R α hσ hα hT hTR)

lemma psk_tail_bound_pos (σ T R α : ℝ) (hσ : 0 < σ) (hα : α ≠ 0) (hT : 0 < T) (hTR : T ≤ R) :
    ‖pskInt σ R α - pskInt σ T α‖ ≤ 6 / (|α| * T) := by
  rw [psk_int_split σ T R α (ne_of_gt hσ)]
  calc
    ‖(∫ t in T..R, pskKern σ α t) + ∫ t in -R..-T, pskKern σ α t‖
        ≤ ‖∫ t in T..R, pskKern σ α t‖ + ‖∫ t in -R..-T, pskKern σ α t‖ := norm_add_le _ _
    _ ≤ 3 / (|α| * T) + 3 / (|α| * T) := by
      exact add_le_add
        (by simpa [pskKern] using (perronKernelSigma_oscTail_pos σ T R α hσ hα hT hTR))
        (psk_neg_tail_pos σ T R α hσ hα hT hTR)
    _ = 6 / (|α| * T) := by ring

lemma pskBound32_pos (σ T α : ℝ) (hσ : 0 < σ) (hT : 0 < T) (hα : α ≠ 0) :
    ‖pskInt σ T α - (if 0 < α then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0)‖
      ≤ 32 * min 1 (1 / (T * |α|)) := by
  let V : ℂ := if 0 < α then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑α)) else 0
  have hconv : Tendsto (fun R : ℝ => pskInt σ R α) atTop (𝓝 V) := by
    simpa [V, pskInt, pskKern] using (perronKernelSigma_tendsto σ α hσ hα)
  have hδpos : 0 < T * |α| := mul_pos hT (abs_pos.mpr hα)
  by_cases hδle : T * |α| ≤ 1
  · have hmin : min 1 (1 / (T * |α|)) = 1 := by
      rw [min_eq_left]
      rw [one_le_div₀ hδpos]
      exact hδle
    rw [hmin]
    have hreg : ‖pskInt σ T α‖ ≤ Real.pi + 2 := by
      have hb : ‖pskInt σ T α‖ ≤ Real.pi + 2 * |α| * T := by
        simpa [pskInt, pskKern] using (perronKernelSigma_regionBound σ T α hσ hT.le)
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
    have htail : ∀ R : ℝ, T ≤ R → ‖pskInt σ R α - pskInt σ T α‖ ≤ 6 / (|α| * T) :=
      fun R hR => psk_tail_bound_pos σ T R α hσ hα hT hR
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
      rw [div_eq_mul_inv, one_div]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    simpa [V] using hmain'.trans hcmp

end Commons.Analysis.Complex

namespace Commons.Analysis.Complex

open Commons.Analysis.Fourier

/-- The Perron step kernel. -/
noncomputable def stepKern (σ T z : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
    Complex.exp ((((σ : ℂ) + (t : ℂ) * Complex.I)) * (Complex.log (z : ℂ)))
      / (((σ : ℂ) + (t : ℂ) * Complex.I)))

theorem perronStep_deviation_pos (σ T z : ℝ) (hσ : 0 < σ) (hT : 0 < T) (hz : 0 < z)
    (hz1 : z ≠ 1) :
    ‖stepKern σ T z - (if 1 < z then (1 : ℂ) else 0)‖
      ≤ (32 / (2 * Real.pi)) * (z ^ σ) * min 1 (1 / (T * |Real.log z|)) := by
  unfold stepKern
  have hrewrite : (∫ (t : ℝ) in -T..T,
        Complex.exp ((((σ : ℂ) + (t : ℂ) * Complex.I)) * (Complex.log (z : ℂ)))
          / (((σ : ℂ) + (t : ℂ) * Complex.I)))
      = ∫ (t : ℝ) in -T..T,
          Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Complex.log (z : ℂ)))
            / ((σ : ℂ) + Complex.I * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by ring
    rw [h1]
  rw [hrewrite]
  have hα : Real.log z ≠ 0 := by
    intro h0
    apply hz1
    have hzexp : Real.exp (Real.log z) = z := Real.exp_log hz
    calc
      z = Real.exp (Real.log z) := hzexp.symm
      _ = 1 := by rw [h0]; norm_num
  have hb32 : ‖pskInt σ T (Real.log z)
        - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
      ≤ 32 * min 1 (1 / (T * |Real.log z|)) :=
    pskBound32_pos σ T (Real.log z) hσ hT hα
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
  have hscal_nonneg : 0 ≤ z ^ σ / (2 * Real.pi) := by positivity
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
  rw [hcontent, hnormfac]
  have hfin : (z ^ σ / (2 * Real.pi)) * ‖pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
        ≤ (32 / (2 * Real.pi)) * z ^ σ * min 1 (1 / (T * |Real.log z|)) := by
    calc
      (z ^ σ / (2 * Real.pi)) * ‖pskInt σ T (Real.log z)
            - (if 0 < Real.log z then 2 * ↑Real.pi * cexp (-((σ : ℂ) * ↑(Real.log z))) else 0)‖
          ≤ (z ^ σ / (2 * Real.pi)) * (32 * min 1 (1 / (T * |Real.log z|))) := by
            exact mul_le_mul_of_nonneg_left hb32 hscal_nonneg
      _ = (32 / (2 * Real.pi)) * z ^ σ * min 1 (1 / (T * |Real.log z|)) := by ring
  exact hfin

end Commons.Analysis.Complex

namespace Commons.Analysis.Complex

open Commons.Analysis.Fourier

lemma exp_cpow_ofReal_pos (z : ℝ) (hz : 0 < z) (s : ℂ) :
    ((z : ℂ) ^ s) = Complex.exp (s * Complex.log (z : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero]
  · congr 1
    rw [mul_comm]
  · exact_mod_cast hz.ne'

lemma div_cpow_ofReal_div (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (s : ℂ) :
    (a : ℂ) ^ s / (b : ℂ) ^ s = ((a / b : ℝ) : ℂ) ^ s := by
  calc
    (a : ℂ) ^ s / (b : ℂ) ^ s = (((a : ℂ) / (b : ℂ)) ^ s) :=
      (Complex.div_cpow_ofReal_nonneg ha hb s).symm
    _ = ((a / b : ℝ) : ℂ) ^ s := by
      congr 1
      rw [← Complex.ofReal_div]

/-- The `n`-th summand whose series expands the Perron integrand. -/
noncomputable def perronF (a : ℕ → ℂ) (c x : ℝ) (n : ℕ) : ℝ → ℂ :=
  fun t => if n = 0 then 0 else
    a n * Complex.exp ((((c : ℂ) + (t : ℂ) * Complex.I)) * Complex.log (((x / (n : ℝ)) : ℝ) : ℂ))
      / (((c : ℂ) + (t : ℂ) * Complex.I))


lemma norm_sline_ge (c : ℝ) (hc : 0 < c) (y : ℝ) : c ≤ ‖((c : ℂ) + (y : ℂ) * Complex.I)‖ := by
  have hsq : c ^ 2 ≤ ‖((c : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [sq_nonneg y]
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (le_of_lt hc), abs_of_nonneg (norm_nonneg _)] at h

lemma sline_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre
  exact hc.ne' hre

lemma norm_exp_perron (c x : ℝ) (hx : 0 < x) (n : ℕ) (hn : n ≠ 0) (μ : ℝ) :
    ‖Complex.exp ((((c : ℂ) + (μ : ℂ) * Complex.I)) * Complex.log (((x / (n : ℝ)) : ℝ) : ℂ))‖
      = (x / (n : ℝ)) ^ c := by
  rw [Complex.norm_exp, ← Complex.ofReal_log (div_nonneg hx.le (Nat.cast_nonneg n))]
  have hy : 0 < x / (n : ℝ) := div_pos hx (by exact_mod_cast (Nat.pos_of_ne_zero hn))
  have hre : (((c : ℂ) + (μ : ℂ) * Complex.I) * ((Real.log (x / (n : ℝ)) : ℝ) : ℂ)).re
      = c * Real.log (x / (n : ℝ)) := by
    rw [Complex.mul_re]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [hre, Real.rpow_def_of_pos hy]
  congr 1
  ring

lemma continuous_perronF (a : ℕ → ℂ) (c x : ℝ) (hc : 0 < c) (n : ℕ) :
    Continuous (perronF a c x n) := by
  by_cases hn : n = 0
  · subst hn
    have h0 : perronF a c x 0 = fun _ => (0 : ℂ) := by
      funext t; simp [perronF]
    rw [h0]
    exact continuous_const
  · have hfun : perronF a c x n = fun t : ℝ =>
        a n * Complex.exp ((((c : ℂ) + (t : ℂ) * Complex.I))
            * Complex.log (((x / (n : ℝ)) : ℝ) : ℂ))
          / (((c : ℂ) + (t : ℂ) * Complex.I)) := by
      funext t; simp [perronF, hn]
    rw [hfun]
    refine Continuous.div₀ ?_ ?_ ?_
    · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
    · fun_prop
    · intro t
      exact sline_ne_zero c hc t

lemma perronF_term (a : ℕ → ℂ) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) (n : ℕ) (t : ℝ) :
    LSeries.term a (((c : ℂ) + (t : ℂ) * Complex.I)) n
        * ((x : ℂ) ^ (((c : ℂ) + (t : ℂ) * Complex.I))) / (((c : ℂ) + (t : ℂ) * Complex.I))
      = perronF a c x n t := by
  by_cases hn : n = 0
  · subst hn
    simp [perronF, LSeries.term]
  · have hy : 0 < x / (n : ℝ) := div_pos hx (by exact_mod_cast (Nat.pos_of_ne_zero hn))
    simp only [perronF, hn, if_false]
    rw [LSeries.term_of_ne_zero hn]
    calc
      a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
          = a n * ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
              / ((n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)))
              / ((c : ℂ) + (t : ℂ) * Complex.I) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ = a n * ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
              / (((n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)))
              / ((c : ℂ) + (t : ℂ) * Complex.I) := by
            rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring]
      _ = a n * ((((x / (n : ℝ)) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I))
              / ((c : ℂ) + (t : ℂ) * Complex.I) := by
            rw [div_cpow_ofReal_div x (n : ℝ) hx.le (Nat.cast_nonneg n)]
      _ = a n * Complex.exp ((((c : ℂ) + (t : ℂ) * Complex.I))
              * Complex.log (((x / (n : ℝ)) : ℝ) : ℂ))
              / ((c : ℂ) + (t : ℂ) * Complex.I) := by
            rw [exp_cpow_ofReal_pos (x / (n : ℝ)) hy]

end Commons.Analysis.Complex

namespace Commons.Analysis.Complex

open Commons.Analysis.Fourier

lemma perron_series_expansion (a : ℕ → ℂ) (c x T : ℝ) (hc : 0 < c) (hx : 0 < x)
    (h : Summable (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c)) :
    (1 / (2 * Real.pi)) *
        (∫ t in (-T)..T,
          LSeries a ((c : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            / ((c : ℂ) + (t : ℂ) * Complex.I))
      = ∑' n : ℕ, (if n = 0 then 0 else a n * stepKern c T (x / (n : ℝ))) := by
  have hpt : ∀ t : ℝ,
      LSeries a ((c : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I) = ∑' n : ℕ, perronF a c x n t := by
    intro t
    rw [LSeries, div_eq_mul_inv]
    rw [← tsum_mul_right]
    rw [← tsum_mul_right]
    refine tsum_congr (fun n => ?_)
    simpa only [div_eq_mul_inv] using perronF_term a c x hc hx n t
  let FC : ℕ → C(ℝ, ℂ) := fun n => ⟨perronF a c x n, continuous_perronF a c x hc n⟩
  let K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc (-T) T, isCompact_uIcc⟩
  let b : ℕ → ℝ := fun n => (x ^ c / c) * (‖a n‖ / (n : ℝ) ^ c)
  have hb : Summable b := by
    simpa [b] using h.mul_left (x ^ c / c)
  have hbnn : ∀ n : ℕ, 0 ≤ b n := by
    intro n
    simp only [b]
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg hx.le c) hc.le)
      (div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) c))
  have hsup : ∀ n : ℕ, ‖(FC n).restrict K‖ ≤ b n := by
    intro n
    rw [ContinuousMap.norm_le _ (hbnn n)]
    intro y
    change ‖perronF a c x n (y : ℝ)‖ ≤ b n
    by_cases hn : n = 0
    · subst hn
      have : perronF a c x 0 (y : ℝ) = 0 := by simp [perronF]
      rw [this, norm_zero]
      exact hbnn 0
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hper : perronF a c x n (y : ℝ)
          = a n * Complex.exp ((((c : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
              * Complex.log (((x / (n : ℝ)) : ℝ) : ℂ)) / (((c : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := by
        simp [perronF, hn]
      rw [hper]
      have hnorm : ‖a n * Complex.exp ((((c : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
              * Complex.log (((x / (n : ℝ)) : ℝ) : ℂ)) / (((c : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
          = ‖a n‖ * (x / (n : ℝ)) ^ c / ‖((c : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ := by
        rw [norm_div, norm_mul, norm_exp_perron c x hx n hn (y : ℝ)]
      rw [hnorm]
      have hsge : c ≤ ‖((c : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ := norm_sline_ge c hc (y : ℝ)
      have hsc : 0 < ‖((c : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ := lt_of_lt_of_le hc hsge
      calc
        ‖a n‖ * (x / (n : ℝ)) ^ c / ‖((c : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
            ≤ ‖a n‖ * (x / (n : ℝ)) ^ c / c := by
              apply div_le_div_of_nonneg_left _ hc hsge
              exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (div_nonneg hx.le hnpos.le) c)
        _ = b n := by
              simp only [b]
              rw [Real.div_rpow hx.le (Nat.cast_nonneg n)]
              ring
  have hFC_sum : Summable (fun n : ℕ => ‖(FC n).restrict K‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hsup hb
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (f := FC)
    (a := -T) (b := T) hFC_sum
  have hfun : (fun t : ℝ => LSeries a ((c : ℂ) + (t : ℂ) * Complex.I)
        * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I))
      = fun t : ℝ => ∑' n : ℕ, (FC n) t := by
    funext t
    rw [hpt t]
    exact tsum_congr (fun n => rfl)
  have hterm : ∀ n : ℕ,
      (1 / (2 * Real.pi)) * (∫ t in (-T)..T, (FC n) t)
        = (if n = 0 then 0 else a n * stepKern c T (x / (n : ℝ))) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have h0 : (fun t : ℝ => (FC 0) t) = fun _ => (0 : ℂ) := by
        funext t; simp [FC, perronF]
      rw [h0, intervalIntegral.integral_zero]
      simp
    · simp only [hn, if_false]
      have hff : (fun t : ℝ => (FC n) t) = fun t : ℝ =>
          a n * (Complex.exp ((((c : ℂ) + (t : ℂ) * Complex.I))
              * Complex.log (((x / (n : ℝ)) : ℝ) : ℂ)) / (((c : ℂ) + (t : ℂ) * Complex.I))) := by
        funext t; simp [FC, perronF, hn]; ring
      rw [hff, intervalIntegral.integral_const_mul]
      rw [stepKern]
      ring
  calc
    (1 / (2 * Real.pi)) *
        (∫ t in (-T)..T,
          LSeries a ((c : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            / ((c : ℂ) + (t : ℂ) * Complex.I))
        = (1 / (2 * Real.pi)) * (∫ t in (-T)..T, ∑' n : ℕ, (FC n) t) := by rw [hfun]
    _ = (1 / (2 * Real.pi)) * (∑' n : ℕ, ∫ t in (-T)..T, (FC n) t) := by rw [← hswap]
    _ = ∑' n : ℕ, (1 / (2 * Real.pi)) * (∫ t in (-T)..T, (FC n) t) := by rw [tsum_mul_left]
    _ = ∑' n : ℕ, (if n = 0 then 0 else a n * stepKern c T (x / (n : ℝ))) :=
          tsum_congr hterm

end Commons.Analysis.Complex

namespace Commons.Analysis.Complex

open Commons.Analysis.Fourier

/-- **The truncated Perron formula.**

There is an absolute constant `C > 0` such that for every `a : ℕ → ℂ`, real `c > 0`, `x > 1`,
`T > 0` with `x` not a natural number and `Σ_n ‖a n‖/n^c < ∞`,

`‖ (1/(2π)) * (∫_{t=-T}^{T} F(c+it) · x^{c+it}/(c+it) dt) - ∑_{1 ≤ n ≤ ⌊x⌋} a n ‖
   ≤ C · ∑_n ‖a n‖ (x/n)^c min(1, 1/(T |log(x/n)|))`,

where `F(s) = ∑'_n a n / n^s = LSeries a s`.

The proof expands the Dirichlet series inside the integral (absolute convergence on the line
`Re s = c`), proves the per-summand sharp-cutoff Perron-kernel estimate
`Commons.Analysis.Complex.perronStep_deviation_pos`, and sums the errors. -/
theorem exists_perron_formula_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (c x T : ℝ),
      0 < c → 1 < x → 0 < T → (∀ n : ℕ, (n : ℝ) ≠ x) →
      Summable (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) →
      ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T,
            (LSeries a ((c : ℂ) + (t : ℂ) * Complex.I))
              * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
              / ((c : ℂ) + (t : ℂ) * Complex.I))
          - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖
        ≤ C * (∑' n : ℕ, ‖a n‖ * (x / (n : ℝ)) ^ c * min 1 (1 / (T * |Real.log (x / (n:ℝ))|))) := by
  refine ⟨32 / (2 * Real.pi), by positivity, ?_⟩
  intro a c x T hc hx1 hT hxnnat hsumm
  have hx : 0 < x := by linarith
  have hfloor_lt : (⌊x⌋₊ : ℝ) < x := by
    rcases lt_or_eq_of_le (Nat.floor_le hx.le) with h | h
    · exact h
    · exact absurd h (hxnnat ⌊x⌋₊)
  let Q : ℕ → ℂ := fun n => if n = 0 then 0 else a n * stepKern c T (x / (n : ℝ))
  let ind : ℕ → ℂ := fun n => if n = 0 then 0 else if (n : ℝ) < x then a n else 0
  let e : ℕ → ℝ := fun n => ‖a n‖ * (x / (n : ℝ)) ^ c * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))
  have hind_zero : ∀ n, n ∉ Finset.Icc 1 ⌊x⌋₊ → ind n = 0 := by
    intro n hn
    simp only [ind]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, if_false]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnnotle : ¬ n ≤ ⌊x⌋₊ := fun hle => hn (Finset.mem_Icc.mpr ⟨hn1, hle⟩)
      have hxle : x ≤ (n : ℝ) := by
        have hlt : ⌊x⌋₊ < n := Nat.lt_of_not_le hnnotle
        have hcast : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
        have hxlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        linarith
      simp only [not_lt.mpr hxle, if_false]
  have hsum_ind : Summable ind := by
    refine (hasSum_sum_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊) ?_).summable
    intro n hn
    exact hind_zero n hn
  have h2 : (∑' n : ℕ, ind n) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (f := ind) (hind_zero)]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hlt : (n : ℝ) < x := lt_of_le_of_lt (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hfloor_lt
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1; omega
    simp [ind, hn0, hlt]
  have he_nonneg : ∀ n, 0 ≤ e n := by
    intro n
    simp only [e]
    exact mul_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (div_nonneg hx.le (Nat.cast_nonneg n)) c))
      (le_min zero_le_one (div_nonneg zero_le_one (mul_nonneg hT.le (abs_nonneg _))))
  have he_le : ∀ n, e n ≤ x ^ c * (‖a n‖ / (n : ℝ) ^ c) := by
    intro n
    simp only [e]
    have hcase : (x / (n : ℝ)) ^ c * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))
        ≤ (x / (n : ℝ)) ^ c := by
      have hle1 : min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) ≤ 1 := min_le_left _ _
      nlinarith [Real.rpow_nonneg (div_nonneg hx.le (Nat.cast_nonneg n)) c]
    calc
      ‖a n‖ * (x / (n : ℝ)) ^ c * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))
          = ‖a n‖ * ((x / (n : ℝ)) ^ c * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) := by ring
      _ ≤ ‖a n‖ * (x / (n : ℝ)) ^ c := mul_le_mul_of_nonneg_left hcase (norm_nonneg _)
      _ = x ^ c * (‖a n‖ / (n : ℝ) ^ c) := by
            rw [Real.div_rpow hx.le (Nat.cast_nonneg n)]
            ring
  have hsum_e : Summable e :=
    Summable.of_nonneg_of_le he_nonneg he_le (hsumm.mul_left (x ^ c))
  have hQt : ∀ n, ‖Q n - ind n‖ ≤ (32 / (2 * Real.pi)) * e n := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      have hQ0 : Q 0 = 0 := by simp [Q]
      have hind0 : ind 0 = 0 := by simp [ind]
      have he0 : e 0 = 0 := by
        simp only [e, Nat.cast_zero, div_zero, Real.zero_rpow hc.ne', Real.log_zero, abs_zero,
          mul_zero, zero_mul, min_eq_right zero_le_one]
      rw [hQ0, hind0, sub_zero, norm_zero, he0, mul_zero]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
      have hQn : Q n = a n * stepKern c T (x / (n : ℝ)) := by simp [Q, hn0]
      have hindn : ind n = if (n : ℝ) < x then a n else 0 := by simp [ind, hn0]
      have hzpos : 0 < x / (n : ℝ) := div_pos hx hnpos
      have hz1 : x / (n : ℝ) ≠ 1 := by
        intro h
        apply hxnnat n
        have h' := congrArg (fun y : ℝ => y * (n : ℝ)) h
        rw [div_mul_cancel₀ _ hnpos.ne'] at h'
        simpa using h'.symm
      have hdev := perronStep_deviation_pos c T (x / (n : ℝ)) hc hT hzpos hz1
      have hif : (1 < x / (n : ℝ)) ↔ (n : ℝ) < x := by
        rw [lt_div_iff₀ hnpos]; simp
      have hdiff : Q n - ind n
          = a n * (stepKern c T (x / (n : ℝ)) - (if (n : ℝ) < x then (1 : ℂ) else 0)) := by
        rw [hQn, hindn]
        by_cases hlt : (n : ℝ) < x <;> simp [hlt] <;> ring
      rw [hdiff, norm_mul]
      calc
        ‖a n‖ * ‖stepKern c T (x / (n : ℝ)) - (if (n : ℝ) < x then (1 : ℂ) else 0)‖
            = ‖a n‖ * ‖stepKern c T (x / (n : ℝ)) - (if 1 < x / (n : ℝ) then (1 : ℂ) else 0)‖ := by
              rw [if_congr hif rfl rfl]
        _ ≤ ‖a n‖ * ((32 / (2 * Real.pi)) * (x / (n : ℝ)) ^ c
              * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) :=
              mul_le_mul_of_nonneg_left hdev (norm_nonneg _)
        _ = (32 / (2 * Real.pi)) * e n := by simp only [e]; ring
  have hsub_sum : Summable (fun n => Q n - ind n) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hQt (hsum_e.mul_left _)
  have hQ_sum : Summable Q := by
    have := hsub_sum.add hsum_ind
    simpa [sub_add_cancel] using this
  have hnorm_sub_sum : Summable (fun n => ‖Q n - ind n‖) := hsub_sum.norm
  have h1 : (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
            (LSeries a ((c : ℂ) + (t : ℂ) * Complex.I))
              * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
              / ((c : ℂ) + (t : ℂ) * Complex.I)) = ∑' n : ℕ, Q n := by
    simpa [Q] using perron_series_expansion a c x T hc hx hsumm
  calc
    ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T,
            (LSeries a ((c : ℂ) + (t : ℂ) * Complex.I))
              * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
              / ((c : ℂ) + (t : ℂ) * Complex.I))
          - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖
        = ‖∑' n : ℕ, Q n - ∑' n : ℕ, ind n‖ := by rw [h1, ← h2]
    _ = ‖∑' n : ℕ, (Q n - ind n)‖ := by rw [Summable.tsum_sub hQ_sum hsum_ind]
    _ ≤ ∑' n : ℕ, ‖Q n - ind n‖ := norm_tsum_le_tsum_norm hnorm_sub_sum
    _ ≤ ∑' n : ℕ, (32 / (2 * Real.pi)) * e n :=
          hasSum_le hQt hnorm_sub_sum.hasSum (hsum_e.mul_left _).hasSum
    _ = (32 / (2 * Real.pi)) * ∑' n : ℕ, e n := tsum_mul_left

end Commons.Analysis.Complex
