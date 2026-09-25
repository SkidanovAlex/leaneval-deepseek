import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_rh
import Submission.Commons.Analysis.Real.integrableOn_log10_div_sqrt
import Submission.Commons.NumberTheory.Chebyshev.theta_measurable
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.NumberTheory.Zeta.chebyshevTheta_sub_id_rh_bound

namespace Commons.NumberTheory.Chebyshev

open MeasureTheory Set Filter
open scoped Topology BigOperators

private lemma mul_sqrt_eq_rpow (t : ℝ) (ht : 0 < t) :
    t * Real.sqrt t = t ^ (3/2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  have h : t ^ (1:ℝ) * t ^ (1/2:ℝ) = t ^ ((1:ℝ) + 1/2) := (Real.rpow_add ht 1 (1/2)).symm
  rw [Real.rpow_one] at h
  norm_num at h
  exact h

private lemma sqrt_div_sq_eq (t : ℝ) (ht : 0 < t) :
    Real.sqrt t / t ^ 2 = t ^ (-(3/2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub ht]
  norm_num

private lemma rpow_third_div_sq_eq (t : ℝ) (ht : 0 < t) :
    t ^ (1/3 : ℝ) / t ^ 2 = t ^ (-(5/3) : ℝ) := by
  rw [← Real.rpow_two, ← Real.rpow_sub ht]
  norm_num

private lemma norm_mul_logW_le {C a : ℝ} (hC : 0 ≤ C) {t : ℝ} (ht : Real.exp 1 ≤ t)
    (h : |a - t| ≤ C * Real.sqrt t * (Real.log t) ^ 10) :
    ‖(a - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))‖
      ≤ (2 * C) * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hL1 : (1 : ℝ) ≤ Real.log t := by
    have h' := Real.log_le_log (Real.exp_pos 1) ht
    rwa [Real.log_exp] at h'
  have hLpos : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hL1
  have hWnn : 0 ≤ (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by positivity
  have hkey : (Real.log t + 1) * (Real.log t) ^ 8 ≤ 2 * (Real.log t) ^ 10 := by
    have h2 : (Real.log t + 1) ≤ 2 * (Real.log t) ^ 2 := by
      nlinarith [hL1, sq_nonneg (Real.log t - 1)]
    calc (Real.log t + 1) * (Real.log t) ^ 8 ≤ (2 * (Real.log t) ^ 2) * (Real.log t) ^ 8 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * (Real.log t) ^ 10 := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hWnn]
  calc |a - t| * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      ≤ (C * Real.sqrt t * (Real.log t) ^ 10) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) :=
        mul_le_mul_of_nonneg_right h hWnn
    _ = C * ((Real.log t + 1) * (Real.log t) ^ 8) * (Real.sqrt t / t ^ 2) := by
        field_simp
    _ = C * ((Real.log t + 1) * (Real.log t) ^ 8) * t ^ (-(3/2) : ℝ) := by
        rw [sqrt_div_sq_eq t ht0]
    _ ≤ C * (2 * (Real.log t) ^ 10) * t ^ (-(3/2) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt ht0) _)
        exact mul_le_mul_of_nonneg_left hkey hC
    _ = (2 * C) * ((Real.log t) ^ 10 * t ^ (-(3/2) : ℝ)) := by ring
    _ = (2 * C) * ((Real.log t) ^ 10 / (t * Real.sqrt t)) := by
        have h2 : t ^ (-(3/2) : ℝ) = (t ^ (3/2:ℝ))⁻¹ := Real.rpow_neg (le_of_lt ht0) (3/2)
        rw [h2, mul_sqrt_eq_rpow t ht0]
        simp only [div_eq_mul_inv]

private lemma sqrt_mul_logW_le {t : ℝ} (ht : 0 < t) (hL : 1 ≤ Real.log t) :
    Real.sqrt t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) ≤ 2 * t ^ (-(3/2) : ℝ) := by
  have hLpos : 0 < Real.log t := by linarith
  have hfac : Real.sqrt t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = ((Real.log t + 1) / (Real.log t) ^ 2) * (Real.sqrt t / t ^ 2) := by
    field_simp
  rw [hfac, sqrt_div_sq_eq t ht]
  have h2 : (Real.log t + 1) / (Real.log t) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hL, sq_nonneg (Real.log t - 1)]
  calc ((Real.log t + 1) / (Real.log t) ^ 2) * t ^ (-(3/2) : ℝ)
      ≤ 2 * t ^ (-(3/2) : ℝ) := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt ht) _)

private lemma third_mul_logW_le {t : ℝ} (ht : 0 < t) (hL : 1 ≤ Real.log t) :
    t ^ (1/3 : ℝ) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) ≤ 2 * t ^ (-(5/3) : ℝ) := by
  have hLpos : 0 < Real.log t := by linarith
  have hfac : t ^ (1/3 : ℝ) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = ((Real.log t + 1) / (Real.log t) ^ 2) * (t ^ (1/3 : ℝ) / t ^ 2) := by
    field_simp
  rw [hfac, rpow_third_div_sq_eq t ht]
  have h2 : (Real.log t + 1) / (Real.log t) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hL, sq_nonneg (Real.log t - 1)]
  calc ((Real.log t + 1) / (Real.log t) ^ 2) * t ^ (-(5/3) : ℝ)
      ≤ 2 * t ^ (-(5/3) : ℝ) := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt ht) _)

private lemma sqrt_mul_W_eq (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) :
    Real.sqrt t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = t ^ (-(3/2) : ℝ) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹) := by
  have hlog0 : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht ht1
  have h3 : (Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹ = (Real.log t + 1) / (Real.log t)^2 := by
    field_simp
  rw [h3]
  have h2 : Real.sqrt t / t ^ 2 = t ^ (-(3/2) : ℝ) := sqrt_div_sq_eq t ht
  calc Real.sqrt t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = ((Real.log t + 1) / (Real.log t) ^ 2) * (Real.sqrt t / t ^ 2) := by
        field_simp
    _ = ((Real.log t + 1) / (Real.log t) ^ 2) * t ^ (-(3/2) : ℝ) := by rw [h2]
    _ = t ^ (-(3/2) : ℝ) * ((Real.log t + 1) / (Real.log t)^2) := by ring

private lemma third_mul_W_eq (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) :
    t ^ (1/3 : ℝ) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = t ^ (-(5/3) : ℝ) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹) := by
  have hlog0 : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht ht1
  have h3 : (Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹ = (Real.log t + 1) / (Real.log t)^2 := by
    field_simp
  rw [h3]
  have h2 : t ^ (1/3 : ℝ) / t ^ 2 = t ^ (-(5/3) : ℝ) := rpow_third_div_sq_eq t ht
  calc t ^ (1/3 : ℝ) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      = ((Real.log t + 1) / (Real.log t) ^ 2) * (t ^ (1/3 : ℝ) / t ^ 2) := by
        field_simp
    _ = ((Real.log t + 1) / (Real.log t) ^ 2) * t ^ (-(5/3) : ℝ) := by rw [h2]
    _ = t ^ (-(5/3) : ℝ) * ((Real.log t + 1) / (Real.log t)^2) := by ring

theorem theta_integral_lower_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (∫ t in Set.Ioi x, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      ≥ (∫ t in Set.Ioi x, (Chebyshev.psi t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
        - ((∫ t in Set.Ioi x, t ^ (-(3 / 2) : ℝ) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹))
           + C * (∫ t in Set.Ioi x, t ^ (-(5 / 3) : ℝ) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹))) := by
  obtain ⟨Cθ, hCθpos, x₀θ, hθ⟩ := Commons.NumberTheory.Zeta.chebyshevTheta_sub_id_rh_bound h
  obtain ⟨Cψ, hCψpos, x₀ψ, hψ⟩ := Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound h
  obtain ⟨C1, hC1pos, x₀1, hψθ⟩ := Commons.NumberTheory.Chebyshev.psi_sub_theta_rh h
  refine ⟨C1, hC1pos, max (max (max x₀θ x₀ψ) x₀1) (Real.exp 1), ?_⟩
  intro x hx
  set W : ℝ → ℝ := fun t => (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) with hW
  set GG : ℝ → ℝ := fun t => t ^ (-(3 / 2) : ℝ) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹) with hGG
  set HH : ℝ → ℝ := fun t => t ^ (-(5 / 3) : ℝ) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹) with hHH
  show (∫ t in Set.Ioi x, (Chebyshev.theta t - t) * W t)
      ≥ (∫ t in Set.Ioi x, (Chebyshev.psi t - t) * W t)
        - ((∫ t in Set.Ioi x, GG t) + C1 * (∫ t in Set.Ioi x, HH t))
  have hxθ : x₀θ ≤ x :=
    le_trans (le_trans (le_trans (le_max_left x₀θ x₀ψ) (le_max_left (max x₀θ x₀ψ) x₀1))
      (le_max_left (max (max x₀θ x₀ψ) x₀1) (Real.exp 1))) hx
  have hxψ : x₀ψ ≤ x :=
    le_trans (le_trans (le_trans (le_max_right x₀θ x₀ψ) (le_max_left (max x₀θ x₀ψ) x₀1))
      (le_max_left (max (max x₀θ x₀ψ) x₀1) (Real.exp 1))) hx
  have hx1 : x₀1 ≤ x :=
    le_trans (le_trans (le_max_right (max x₀θ x₀ψ) x₀1)
      (le_max_left (max (max x₀θ x₀ψ) x₀1) (Real.exp 1))) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right (max (max x₀θ x₀ψ) x₀1) (Real.exp 1)) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hxgt1 : (1 : ℝ) < x := by linarith [Real.exp_one_gt_two, hxe]
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_of_lt Real.exp_one_gt_two) hxe
  have hlog1 : ∀ t ∈ Set.Ioi x, (1 : ℝ) ≤ Real.log t := by
    intro t ht
    have h' := Real.log_le_log (Real.exp_pos 1) (le_trans hxe (le_of_lt ht))
    rwa [Real.log_exp] at h'
  have hWmeas : Measurable W := by rw [hW]; fun_prop
  have hθmeas : Measurable Chebyshev.theta := theta_measurable
  have hψmeas : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
  -- integrability of `(θ t - t) * W t`
  have hf1 : IntegrableOn (fun t => (Chebyshev.theta t - t) * W t) (Set.Ioi x) := by
    have hdom : IntegrableOn (fun t : ℝ => (2 * Cθ) * ((Real.log t) ^ 10 / (t * Real.sqrt t)))
        (Set.Ioi x) :=
      Integrable.const_mul (Commons.Analysis.Real.integrableOn_log10_div_sqrt (a := x) hx2) (2 * Cθ)
    refine hdom.mono' ((hθmeas.sub measurable_id).mul hWmeas).aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact norm_mul_logW_le hCθpos.le (le_trans hxe (le_of_lt ht))
      (hθ t (le_trans hxθ (le_of_lt ht)))
  -- integrability of `(ψ t - t) * W t`
  have hf2 : IntegrableOn (fun t => (Chebyshev.psi t - t) * W t) (Set.Ioi x) := by
    have hdom : IntegrableOn (fun t : ℝ => (2 * Cψ) * ((Real.log t) ^ 10 / (t * Real.sqrt t)))
        (Set.Ioi x) :=
      Integrable.const_mul (Commons.Analysis.Real.integrableOn_log10_div_sqrt (a := x) hx2) (2 * Cψ)
    refine hdom.mono' ((hψmeas.sub measurable_id).mul hWmeas).aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact norm_mul_logW_le hCψpos.le (le_trans hxe (le_of_lt ht))
      (hψ t (le_trans hxψ (le_of_lt ht)))
  -- dominating integrable function `2 t^(-3/2) + 2 C1 t^(-5/3)`
  have hdomB : IntegrableOn (fun t : ℝ => 2 * t ^ (-(3/2) : ℝ) + 2 * C1 * t ^ (-(5/3) : ℝ))
      (Set.Ioi x) := by
    have h3 : IntegrableOn (fun t : ℝ => t ^ (-(3/2) : ℝ)) (Set.Ioi x) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hx0
    have h5 : IntegrableOn (fun t : ℝ => t ^ (-(5/3) : ℝ)) (Set.Ioi x) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hx0
    exact (Integrable.const_mul h3 2).add (Integrable.const_mul h5 (2 * C1))
  -- integrability of `(ψ t - θ t) * W t`
  have hf3 : IntegrableOn (fun t => (Chebyshev.psi t - Chebyshev.theta t) * W t) (Set.Ioi x) := by
    refine hdomB.mono' ((hψmeas.sub hθmeas).mul hWmeas).aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
    have hL1 := hlog1 t ht
    have hLpos : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hL1
    have hWnn : 0 ≤ W t := by rw [hW]; positivity
    have hnn : 0 ≤ Chebyshev.psi t - Chebyshev.theta t := sub_nonneg.mpr (Chebyshev.theta_le_psi t)
    have hb : Chebyshev.psi t - Chebyshev.theta t ≤ Real.sqrt t + C1 * t ^ (1/3 : ℝ) := by
      have hbb := (hψθ t (le_trans hx1 (le_of_lt ht))).2
      linarith
    have hsqrtW : Real.sqrt t * W t ≤ 2 * t ^ (-(3/2) : ℝ) := by
      rw [hW]; exact sqrt_mul_logW_le ht0 hL1
    have hthirdW : t ^ (1/3 : ℝ) * W t ≤ 2 * t ^ (-(5/3) : ℝ) := by
      rw [hW]; exact third_mul_logW_le ht0 hL1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn hWnn)]
    calc (Chebyshev.psi t - Chebyshev.theta t) * W t
        ≤ (Real.sqrt t + C1 * t ^ (1/3 : ℝ)) * W t := mul_le_mul_of_nonneg_right hb hWnn
      _ = Real.sqrt t * W t + C1 * (t ^ (1/3 : ℝ) * W t) := by ring
      _ ≤ 2 * t ^ (-(3/2) : ℝ) + C1 * (2 * t ^ (-(5/3) : ℝ)) :=
            add_le_add hsqrtW (mul_le_mul_of_nonneg_left hthirdW hC1pos.le)
      _ = 2 * t ^ (-(3/2) : ℝ) + 2 * C1 * t ^ (-(5/3) : ℝ) := by ring
  -- integrability of `√t * W t`
  have hIg : IntegrableOn (fun t => Real.sqrt t * W t) (Set.Ioi x) := by
    have hdom : IntegrableOn (fun t : ℝ => 2 * t ^ (-(3/2) : ℝ)) (Set.Ioi x) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) hx0) 2
    refine hdom.mono' ((Real.continuous_sqrt.measurable).mul hWmeas).aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
    have hLpos : 0 < Real.log t := lt_of_lt_of_le zero_lt_one (hlog1 t ht)
    have hWnn : 0 ≤ W t := by rw [hW]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg t) hWnn)]
    rw [hW]; exact sqrt_mul_logW_le ht0 (hlog1 t ht)
  -- integrability of `t^(1/3) * W t`
  have hIh : IntegrableOn (fun t => t ^ (1/3 : ℝ) * W t) (Set.Ioi x) := by
    have hdom : IntegrableOn (fun t : ℝ => 2 * t ^ (-(5/3) : ℝ)) (Set.Ioi x) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) hx0) 2
    have hm : Measurable (fun t => t ^ (1/3 : ℝ) * W t) := by rw [hW]; fun_prop
    refine hdom.mono' hm.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
    have hLpos : 0 < Real.log t := lt_of_lt_of_le zero_lt_one (hlog1 t ht)
    have hWnn : 0 ≤ W t := by rw [hW]; positivity
    have h13 : 0 ≤ t ^ (1/3 : ℝ) := Real.rpow_nonneg (le_of_lt ht0) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h13 hWnn)]
    rw [hW]; exact third_mul_logW_le ht0 (hlog1 t ht)
  -- integrability of `(√t + C1 t^(1/3)) * W t`
  have hIplus : IntegrableOn (fun t => (Real.sqrt t + C1 * t ^ (1/3 : ℝ)) * W t) (Set.Ioi x) := by
    have hm : Measurable (fun t => (Real.sqrt t + C1 * t ^ (1/3 : ℝ)) * W t) := by rw [hW]; fun_prop
    refine hdomB.mono' hm.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
    have hL1 := hlog1 t ht
    have hLpos : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hL1
    have hWnn : 0 ≤ W t := by rw [hW]; positivity
    have hsqrtW : Real.sqrt t * W t ≤ 2 * t ^ (-(3/2) : ℝ) := by
      rw [hW]; exact sqrt_mul_logW_le ht0 hL1
    have hthirdW : t ^ (1/3 : ℝ) * W t ≤ 2 * t ^ (-(5/3) : ℝ) := by
      rw [hW]; exact third_mul_logW_le ht0 hL1
    have h13 : 0 ≤ t ^ (1/3 : ℝ) := Real.rpow_nonneg (le_of_lt ht0) _
    have hnn : 0 ≤ Real.sqrt t + C1 * t ^ (1/3 : ℝ) := by
      have := Real.sqrt_nonneg t; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn hWnn)]
    calc (Real.sqrt t + C1 * t ^ (1/3 : ℝ)) * W t
        = Real.sqrt t * W t + C1 * (t ^ (1/3 : ℝ) * W t) := by ring
      _ ≤ 2 * t ^ (-(3/2) : ℝ) + C1 * (2 * t ^ (-(5/3) : ℝ)) :=
            add_le_add hsqrtW (mul_le_mul_of_nonneg_left hthirdW hC1pos.le)
      _ = 2 * t ^ (-(3/2) : ℝ) + 2 * C1 * t ^ (-(5/3) : ℝ) := by ring
  -- pointwise bound and monotonicity
  have hmono : (∫ t in Set.Ioi x, (Chebyshev.psi t - Chebyshev.theta t) * W t)
      ≤ (∫ t in Set.Ioi x, (Real.sqrt t + C1 * t ^ (1/3 : ℝ)) * W t) := by
    refine setIntegral_mono_on hf3 hIplus measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
    have hLpos : 0 < Real.log t := lt_of_lt_of_le zero_lt_one (hlog1 t ht)
    have hWnn : 0 ≤ W t := by rw [hW]; positivity
    have hb : Chebyshev.psi t - Chebyshev.theta t ≤ Real.sqrt t + C1 * t ^ (1/3 : ℝ) := by
      have hbb := (hψθ t (le_trans hx1 (le_of_lt ht))).2
      linarith
    exact mul_le_mul_of_nonneg_right hb hWnn
  -- splitting the auxiliary integral
  have hsplit : (∫ t in Set.Ioi x, (Real.sqrt t + C1 * t ^ (1/3 : ℝ)) * W t)
      = (∫ t in Set.Ioi x, GG t) + C1 * (∫ t in Set.Ioi x, HH t) := by
    have h2 : IntegrableOn (fun t => C1 * (t ^ (1/3 : ℝ) * W t)) (Set.Ioi x) :=
      Integrable.const_mul hIh C1
    have hidg : ∀ t ∈ Set.Ioi x, Real.sqrt t * W t = GG t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
      have ht1 : t ≠ 1 := by
        intro hh
        have hxt : x ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
        linarith [hxgt1, hxt]
      simpa only [hW, hGG] using sqrt_mul_W_eq t ht0 ht1
    have hidh : ∀ t ∈ Set.Ioi x, t ^ (1/3 : ℝ) * W t = HH t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
      have ht1 : t ≠ 1 := by
        intro hh
        have hxt : x ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
        linarith [hxgt1, hxt]
      simpa only [hW, hHH] using third_mul_W_eq t ht0 ht1
    calc (∫ t in Set.Ioi x, (Real.sqrt t + C1 * t ^ (1/3 : ℝ)) * W t)
        = ∫ t in Set.Ioi x, (Real.sqrt t * W t + C1 * (t ^ (1/3 : ℝ) * W t)) := by
            apply setIntegral_congr_fun measurableSet_Ioi; intro t ht; ring
      _ = (∫ t in Set.Ioi x, Real.sqrt t * W t) + (∫ t in Set.Ioi x, C1 * (t ^ (1/3 : ℝ) * W t)) :=
            integral_add hIg h2
      _ = (∫ t in Set.Ioi x, Real.sqrt t * W t) + C1 * (∫ t in Set.Ioi x, t ^ (1/3 : ℝ) * W t) := by
            rw [integral_const_mul]
      _ = (∫ t in Set.Ioi x, GG t) + C1 * (∫ t in Set.Ioi x, HH t) := by
            rw [setIntegral_congr_fun measurableSet_Ioi hidg,
              setIntegral_congr_fun measurableSet_Ioi hidh]
  -- relating the two main integrals
  have hsub : (∫ t in Set.Ioi x, (Chebyshev.theta t - t) * W t)
        - (∫ t in Set.Ioi x, (Chebyshev.psi t - t) * W t)
      = - (∫ t in Set.Ioi x, (Chebyshev.psi t - Chebyshev.theta t) * W t) := by
    calc (∫ t in Set.Ioi x, (Chebyshev.theta t - t) * W t)
          - (∫ t in Set.Ioi x, (Chebyshev.psi t - t) * W t)
        = ∫ t in Set.Ioi x, ((Chebyshev.theta t - t) * W t - (Chebyshev.psi t - t) * W t) :=
            (integral_sub hf1 hf2).symm
      _ = ∫ t in Set.Ioi x, -((Chebyshev.psi t - Chebyshev.theta t) * W t) := by
            apply setIntegral_congr_fun measurableSet_Ioi; intro t ht; ring
      _ = - (∫ t in Set.Ioi x, (Chebyshev.psi t - Chebyshev.theta t) * W t) := integral_neg _
  linarith [hsub, hmono, hsplit]

end Commons.NumberTheory.Chebyshev
