import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.subordination_rpow`

The subordination identity for the kinetic energy of the dilute Bose gas:

`∫_{t>0} (1 - exp (-(a t))) t ^ (-(3:ℝ)/2) = 2 √π √a`  (`a ≥ 0`).

It is the `s = 1/2` case of the standard Beta/Gamma identity
`∫_{t>0} (1 - exp (-a t)) t ^ (-1-s) dt = Γ(1-s) a^s / s`, obtained here by
integration by parts (`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`) against
the antiderivative `-2 t^{-1/2}` of `t^{-3/2}`, together with the Gamma integral
`∫_{t>0} t^{-1/2} exp (-a t) dt = √π / √a` (`Real.integral_rpow_mul_exp_neg_mul_Ioi`
combined with `Real.Gamma_one_half_eq`).
-/

open MeasureTheory Set Filter

noncomputable section

namespace Work.BoseBoxFock.SqrtKin

/-- `∫_{t>0} t^{-1/2} exp (-a t) dt = √π / √a` for `a > 0` (a Gamma integral). -/
lemma gamma_int_rpow_neg_half (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (-(1 : ℝ) / 2) * Real.exp (-(a * t))
      = Real.sqrt Real.pi / Real.sqrt a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 : ℝ) / 2) (r := a) (by norm_num) ha
  rw [Real.Gamma_one_half_eq] at h
  rw [show (1 : ℝ) / 2 - 1 = -(1 : ℝ) / 2 by norm_num] at h
  have h2 : (1 / a) ^ ((1 : ℝ) / 2) * Real.sqrt Real.pi = Real.sqrt Real.pi / Real.sqrt a := by
    rw [one_div, ← Real.sqrt_eq_rpow, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
  rwa [h2] at h

/-- The subordination integrand `(1 - exp (-(a t))) t^{-3/2}` is integrable on `(0,∞)`
for `a ≥ 0`: it is dominated by `a t^{-1/2}` near `0` and by `t^{-3/2}` near `∞`. -/
lemma integrableOn_one_sub_exp_mul_rpow (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2))
      (Set.Ioi 0) := by
  have hnn : ∀ t : ℝ, 0 < t → 0 ≤ 1 - Real.exp (-(a * t)) := by
    intro t ht
    have h1 : Real.exp (-(a * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht, ha])
    linarith
  have hle1 : ∀ t : ℝ, 0 < t → 1 - Real.exp (-(a * t)) ≤ a * t ^ (1 : ℝ) := by
    intro t ht
    have h1 := Real.add_one_le_exp (-(a * t))
    rw [Real.rpow_one]
    linarith
  have hleft :
      IntegrableOn (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2))
        (Ioc (0 : ℝ) 1) := by
    have hcon : ContinuousOn
        (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)) (Ioc (0 : ℝ) 1) := by
      refine ContinuousOn.mul ?_ ?_
      · fun_prop
      · exact continuous_id.continuousOn.rpow_const (p := -(3 : ℝ) / 2)
          (fun x hx => Or.inl (ne_of_gt hx.1))
    have hg : IntegrableOn (fun t : ℝ => a * t ^ (-(1 : ℝ) / 2)) (Ioc (0 : ℝ) 1) := by
      have h0 : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Ioo (0 : ℝ) 1) :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mpr
          (by norm_num)
      exact ((integrableOn_Ioc_iff_integrableOn_Ioo).mpr h0).const_mul a
    refine Integrable.mono' hg (hcon.aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have htp : 0 ≤ t ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn t ht0) htp)]
    calc (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)
        ≤ (a * t ^ (1 : ℝ)) * t ^ (-(3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (hle1 t ht0) htp
      _ = a * (t ^ (1 : ℝ) * t ^ (-(3 : ℝ) / 2)) := by ring
      _ = a * t ^ (-(1 : ℝ) / 2) := by
            rw [← Real.rpow_add ht0, show (1 : ℝ) + -(3 : ℝ) / 2 = -(1 : ℝ) / 2 by norm_num]
  have hright :
      IntegrableOn (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2))
        (Ioi (1 : ℝ)) := by
    have hcon : ContinuousOn
        (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)) (Ioi (1 : ℝ)) := by
      refine ContinuousOn.mul ?_ ?_
      · fun_prop
      · exact continuous_id.continuousOn.rpow_const (p := -(3 : ℝ) / 2)
          (fun x hx => Or.inl (ne_of_gt (lt_trans zero_lt_one hx)))
    have hg : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine Integrable.mono' hg (hcon.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have htp : 0 ≤ t ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
    have hle : 1 - Real.exp (-(a * t)) ≤ 1 := by
      have h1 := Real.exp_pos (-(a * t))
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn t ht0) htp)]
    calc (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)
        ≤ 1 * t ^ (-(3 : ℝ) / 2) := mul_le_mul_of_nonneg_right hle htp
      _ = t ^ (-(3 : ℝ) / 2) := by rw [one_mul]
  have hAll := integrableOn_union.mpr ⟨hleft, hright⟩
  rw [Ioc_union_Ioi (by norm_num : (1 : ℝ) ≤ max (0 : ℝ) 1),
    min_eq_left (by norm_num : (0 : ℝ) ≤ 1)] at hAll
  exact hAll

/-- `(1 - exp (-(a t))) · (-2 t^{-1/2}) → 0` as `t → 0⁺`, for `a > 0`. -/
lemma tendsto_one_sub_exp_mul_rpow_nhdsGT (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => (1 - Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hg : Tendsto (fun t : ℝ => -2 * a * t ^ ((1 : ℝ) / 2))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    have hc : Tendsto (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (nhds (0 : ℝ))
        (nhds ((0 : ℝ) ^ ((1 : ℝ) / 2))) :=
      (Real.continuousAt_rpow_const 0 ((1 : ℝ) / 2) (Or.inr (by norm_num))).tendsto
    have hc' : Tendsto (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds 0) := by
      have h := hc.mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds (0 : ℝ))
      rwa [Real.zero_rpow (by norm_num : ((1 : ℝ) / 2) ≠ 0)] at h
    simpa using hc'.const_mul (-2 * a)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have hle : 1 - Real.exp (-(a * t)) ≤ a * t := by
      have h1 := Real.add_one_le_exp (-(a * t))
      linarith
    have hneg : -2 * t ^ (-(1 : ℝ) / 2) ≤ 0 := by
      have h1 := Real.rpow_nonneg ht0.le (-(1 : ℝ) / 2)
      linarith
    have h3 : t ^ ((1 : ℝ) / 2) = t * t ^ (-(1 : ℝ) / 2) := by
      rw [show ((1 : ℝ) / 2) = 1 + (-(1 : ℝ) / 2) by norm_num, Real.rpow_add ht0,
        Real.rpow_one]
    calc -2 * a * t ^ ((1 : ℝ) / 2) = (a * t) * (-2 * t ^ (-(1 : ℝ) / 2)) := by
          rw [h3]; ring
      _ ≤ (1 - Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2)) :=
          mul_le_mul_of_nonpos_right hle hneg
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have hnn : 0 ≤ 1 - Real.exp (-(a * t)) := by
      have h1 : Real.exp (-(a * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht0, ha])
      linarith
    have hneg : -2 * t ^ (-(1 : ℝ) / 2) ≤ 0 := by
      have h1 := Real.rpow_nonneg ht0.le (-(1 : ℝ) / 2)
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hnn hneg

/-- `(1 - exp (-(a t))) · (-2 t^{-1/2}) → 0` as `t → +∞`, for `a > 0`. -/
lemma tendsto_one_sub_exp_mul_rpow_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => (1 - Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2)))
      atTop (nhds 0) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(a * t))) atTop (nhds 0) := by
    have h : Tendsto (fun t : ℝ => -a * t) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by linarith : -a < 0)).mpr tendsto_id
    have h2 : Tendsto (fun t : ℝ => -(a * t)) atTop atBot := by
      simpa only [neg_mul] using h
    exact Real.tendsto_exp_atBot.comp h2
  have h1 : Tendsto (fun t : ℝ => 1 - Real.exp (-(a * t))) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hexp
  have h2 : Tendsto (fun t : ℝ => -2 * t ^ (-(1 : ℝ) / 2)) atTop (nhds (-2 * 0)) := by
    have h : Tendsto (fun t : ℝ => t ^ (-((1 : ℝ) / 2))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (y := (1 : ℝ) / 2) (by norm_num)
    have he : (-1 : ℝ) / 2 = -((1 : ℝ) / 2) := by norm_num
    have h' : Tendsto (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) atTop (nhds 0) := by
      simpa only [he] using h
    simpa using h'.const_mul (-2)
  simpa using h1.mul h2

theorem subordination_rpow (a : ℝ) (ha : 0 ≤ a) :
    ∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)
      = 2 * Real.sqrt Real.pi * Real.sqrt a := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp
  have hInt : IntegrableOn (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2))
      (Ioi 0) := integrableOn_one_sub_exp_mul_rpow a ha
  have hu : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => 1 - Real.exp (-(a * t))) (a * Real.exp (-(a * x))) x := by
    intro x hx
    have h₁ : HasDerivAt (fun t : ℝ => -(a * t)) (-a) x := by
      have h : HasDerivAt (fun t : ℝ => a * t) a x := by
        simpa using (hasDerivAt_id x).const_mul a
      exact h.neg
    have h₂ : HasDerivAt (fun t : ℝ => Real.exp (-(a * t)))
        (Real.exp (-(a * x)) * (-a)) x := h₁.exp
    have h₃ : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(a * t)))
        (0 - Real.exp (-(a * x)) * (-a)) x := (hasDerivAt_const x (1 : ℝ)).sub h₂
    have hv : (0 : ℝ) - Real.exp (-(a * x)) * (-a) = a * Real.exp (-(a * x)) := by ring
    rw [hv] at h₃
    exact h₃
  have hv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => -2 * t ^ (-(1 : ℝ) / 2)) (x ^ (-(3 : ℝ) / 2)) x := by
    intro x hx
    have h : HasDerivAt (fun t : ℝ => t ^ (-(1 : ℝ) / 2))
        ((-(1 : ℝ) / 2) * x ^ ((-(1 : ℝ) / 2) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
    have h' := h.const_mul (-2)
    have hv' : -2 * ((-(1 : ℝ) / 2) * x ^ ((-(1 : ℝ) / 2) - 1)) = x ^ (-(3 : ℝ) / 2) := by
      rw [show (-(1 : ℝ) / 2) - 1 = -(3 : ℝ) / 2 by norm_num, ← mul_assoc,
        show (-2 : ℝ) * (-(1 : ℝ) / 2) = 1 by norm_num, one_mul]
    rw [hv'] at h'
    exact h'
  have hGint : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * Real.exp (-(a * t)))
      (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := -(1 : ℝ) / 2)
      (b := a) (by norm_num) (by norm_num) ha_pos
    simpa [Real.rpow_one] using h
  have hu'v : IntegrableOn
      (fun t : ℝ => (a * Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2))) (Ioi 0) := by
    have hA : IntegrableOn
        (fun t : ℝ => (-(2 * a)) * (t ^ (-(1 : ℝ) / 2) * Real.exp (-(a * t)))) (Ioi 0) :=
      hGint.const_mul (-(2 * a))
    refine hA.congr_fun ?_ measurableSet_Ioi
    intro t ht
    ring
  have hz := tendsto_one_sub_exp_mul_rpow_nhdsGT a ha_pos
  have hi := tendsto_one_sub_exp_mul_rpow_atTop a ha_pos
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun t : ℝ => 1 - Real.exp (-(a * t)))
    (v := fun t : ℝ => -2 * t ^ (-(1 : ℝ) / 2))
    (u' := fun t : ℝ => a * Real.exp (-(a * t)))
    (v' := fun t : ℝ => t ^ (-(3 : ℝ) / 2)) hu hv hInt hu'v hz hi
  have hmain : ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)
      = -∫ t in Ioi (0 : ℝ), (a * Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2)) := by
    simpa using hIBP
  have hval : ∫ t in Ioi (0 : ℝ), (a * Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2))
      = -(2 * a) * (Real.sqrt Real.pi / Real.sqrt a) := by
    have hcongr : ∫ t in Ioi (0 : ℝ), (a * Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2))
        = ∫ t in Ioi (0 : ℝ),
            (-(2 * a)) * (t ^ (-(1 : ℝ) / 2) * Real.exp (-(a * t))) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      ring
    rw [hcongr, integral_const_mul, gamma_int_rpow_neg_half a ha_pos]
  have hdiv : a * (Real.sqrt Real.pi / Real.sqrt a) = Real.sqrt Real.pi * Real.sqrt a := by
    rw [← mul_div_assoc, mul_comm a, mul_div_assoc, Real.div_sqrt]
  have hval2 : -(2 * a) * (Real.sqrt Real.pi / Real.sqrt a)
      = -(2 * Real.sqrt Real.pi * Real.sqrt a) := by
    rw [neg_mul, mul_assoc, hdiv, ← mul_assoc]
  calc ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)
      = -∫ t in Ioi (0 : ℝ), (a * Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2)) := hmain
    _ = -(-(2 * a) * (Real.sqrt Real.pi / Real.sqrt a)) := by rw [hval]
    _ = 2 * Real.sqrt Real.pi * Real.sqrt a := by rw [hval2, neg_neg]

end Work.BoseBoxFock.SqrtKin
