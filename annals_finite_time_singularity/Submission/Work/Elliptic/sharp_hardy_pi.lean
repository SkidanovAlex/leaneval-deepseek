/-
Copyright: work module for the Elgindi finite-time singularity project.

# The sharp sine-weighted Hardy inequality on `[0, π]`

For `0 ≤ η < 1` there is `C > 0` such that every `f : ℝ → ℝ` of class `C¹` on `[0, π]`
with `f 0 = f π = 0` satisfies

`∫_0^π f(θ)² / sin(θ)^(2+η) dθ ≤ 4/(1+η)² ∫_0^π f'(θ)² / sin(θ)^η dθ
    + C (∫_0^π f(θ)² dθ + ∫_0^π f'(θ)² dθ)`.

The constant `4/(1+η)²` is the sharp constant of the weighted Hardy inequality with the
power weight `θ`.  The interval `[0,π]` has two singular endpoints; splitting at `π/2`,
on each half one compares `sin θ` with `θ` (via Jordan's inequality) and applies

* `Work.Elliptic.power_hardy` (the sharp power-weight Hardy inequality) and
* `Work.Elliptic.sin_pow_compare` (the pointwise comparison `sin^{-(2+η)} ≤ θ^{-(2+η)} + C sin^{-η}`),

while the right half is the reflection `θ ↦ π - θ` of the left one.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.sin_pow_compare
import Submission.Work.Elliptic.power_hardy
import Submission.Work.Elliptic.power_hardy_bounds
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
import Submission.Work.Elliptic.sin_l2_weight_bound
import Submission.Work.Elliptic.half_pi_sin_hardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Elementary rpow algebra -/

private lemma two_div_pi_rpow_neg (η : ℝ) : (2 / Real.pi) ^ (-η) = (Real.pi / 2) ^ η := by
  have h : (0 : ℝ) < Real.pi / 2 := by positivity
  rw [show (2 / Real.pi : ℝ) = (Real.pi / 2)⁻¹ by rw [inv_div]]
  rw [Real.inv_rpow h.le, Real.rpow_neg h.le, inv_inv]

/-- Jordan's inequality in the form needed: `sin θ ^ (-η) ≤ (π/2)^η θ ^ (-η)` on `(0, π/2]`. -/
private lemma sin_rpow_neg_le {η θ : ℝ} (hη0 : 0 ≤ η) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2) :
    (Real.sin θ) ^ (-η) ≤ (Real.pi / 2) ^ η * θ ^ (-η) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθπ, Real.pi_pos])
  have hle : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0.le hθπ
  have hpos : 0 < 2 / Real.pi * θ := by positivity
  have h1 : (Real.sin θ) ^ (-η) ≤ (2 / Real.pi * θ) ^ (-η) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by linarith : -η ≤ 0)
  have h2 : (2 / Real.pi * θ) ^ (-η) = (Real.pi / 2) ^ η * θ ^ (-η) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / Real.pi) hθ0.le, two_div_pi_rpow_neg]
  rw [← h2]; exact h1

private lemma integral_Icc_eq_interval {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℝ) :
    (∫ x in Set.Icc a b, F x) = ∫ x in a..b, F x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-! ## Integrability on `[0, π/2]` -/

private lemma intervalIntegrable_pi2_of_le_rpow {η K : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hK : 0 ≤ K)
    {g : ℝ → ℝ} (hgc : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ K * θ ^ (-η)) :
    IntervalIntegrable g volume 0 (Real.pi / 2) := by
  have hP : (0 : ℝ) < Real.pi / 2 := by positivity
  have hI : IntegrableOn g (Set.Icc 0 (Real.pi / 2)) volume := by
    refine integrableOn_of_rpow_majorant hη0 hη1 hK hgc (fun θ hθ => ?_)
    have h2 : (0 : ℝ) ≤ (Real.pi / 2 - θ) ^ (-η) := Real.rpow_nonneg (by linarith [hθ.2]) _
    exact le_trans (hb θ hθ) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h2) hK)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hP.le).mpr (hI.mono_set Set.Ioc_subset_Icc_self)

private theorem intervalIntegrable_pi2_three {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) :
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin θ) ^ (-(2 + η))) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η)) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin θ) ^ (-η)) volume 0 (Real.pi / 2) := by
  have hP : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨C, hC0, hbf, hbd⟩ := power_hardy_bounds hP hf h0
  have hfc : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf.continuousOn.mono Set.Ioo_subset_Icc_self
  have hdc : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun t => derivWithin f (Set.Icc 0 (Real.pi / 2)) t)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (hf.continuousOn_derivWithin (uniqueDiffOn_Icc hP) le_rfl).mono Set.Ioo_subset_Icc_self
    refine h1.congr (fun t ht => ?_)
    exact (derivWithin_of_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)).symm
  have hsinpos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.sin θ :=
    fun θ hθ => Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hsc : ContinuousOn (fun θ => (Real.sin θ) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.continuousOn.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hsη : ContinuousOn (fun θ => (Real.sin θ) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.continuousOn.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hK1 : (0 : ℝ) ≤ C ^ 2 * (Real.pi / 2) ^ (2 + η) := by positivity
  have hK2 : (0 : ℝ) ≤ C ^ 2 * (Real.pi / 2) ^ η := by positivity
  have hK3 : (0 : ℝ) ≤ C ^ 2 * (Real.pi / 2) ^ η * (Real.pi / 2) ^ 2 := by positivity
  have hf2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), f θ ^ 2 ≤ C ^ 2 * θ ^ 2 := by
    intro θ hθ
    have h := hbf θ hθ
    calc f θ ^ 2 ≤ (C * θ) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC0 hθ.1.le)]; exact h
      _ = C ^ 2 * θ ^ 2 := by ring
  have hd2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv f θ) ^ 2 ≤ C ^ 2 := by
    intro θ hθ
    have h := hbd θ hθ
    rw [sq_le_sq, abs_of_nonneg hC0]; exact h
  refine ⟨?_, ?_, ?_⟩
  · refine intervalIntegrable_pi2_of_le_rpow hη0 hη1 hK1 (hfc.pow 2 |>.mul hsc) (fun θ hθ => ?_)
    have hw : 0 < (Real.sin θ) ^ (-(2 + η)) := Real.rpow_pos_of_pos (hsinpos θ hθ) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw.le)]
    have h2 := sin_rpow_neg_le (η := 2 + η) (by linarith) hθ.1 (le_of_lt hθ.2)
    calc f θ ^ 2 * (Real.sin θ) ^ (-(2 + η))
        ≤ C ^ 2 * θ ^ 2 * (Real.sin θ) ^ (-(2 + η)) :=
          mul_le_mul_of_nonneg_right (hf2 θ hθ) hw.le
      _ ≤ C ^ 2 * θ ^ 2 * ((Real.pi / 2) ^ (2 + η) * θ ^ (-(2 + η))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C ^ 2 * (Real.pi / 2) ^ (2 + η) * θ ^ (-η) := by
          have hth : θ ^ 2 * θ ^ (-(2 + η)) = θ ^ (-η) := by
            rw [← Real.rpow_natCast θ 2, ← Real.rpow_add hθ.1]
            congr 1; ring
          rw [show C ^ 2 * θ ^ 2 * ((Real.pi / 2) ^ (2 + η) * θ ^ (-(2 + η)))
                = C ^ 2 * (Real.pi / 2) ^ (2 + η) * (θ ^ 2 * θ ^ (-(2 + η))) by ring, hth]
  · refine intervalIntegrable_pi2_of_le_rpow hη0 hη1 hK2 (hdc.pow 2 |>.mul hsη) (fun θ hθ => ?_)
    have hw : 0 < (Real.sin θ) ^ (-η) := Real.rpow_pos_of_pos (hsinpos θ hθ) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw.le)]
    have h2 := sin_rpow_neg_le (η := η) hη0 hθ.1 (le_of_lt hθ.2)
    calc (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η)
        ≤ C ^ 2 * (Real.sin θ) ^ (-η) := mul_le_mul_of_nonneg_right (hd2 θ hθ) hw.le
      _ ≤ C ^ 2 * ((Real.pi / 2) ^ η * θ ^ (-η)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C ^ 2 * (Real.pi / 2) ^ η * θ ^ (-η) := by ring
  · refine intervalIntegrable_pi2_of_le_rpow hη0 hη1 hK3 (hfc.pow 2 |>.mul hsη) (fun θ hθ => ?_)
    have hw : 0 < (Real.sin θ) ^ (-η) := Real.rpow_pos_of_pos (hsinpos θ hθ) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw.le)]
    have h2 := sin_rpow_neg_le (η := η) hη0 hθ.1 (le_of_lt hθ.2)
    have hθ2le : θ ^ 2 ≤ (Real.pi / 2) ^ 2 := by nlinarith [hθ.1, hθ.2, Real.pi_pos]
    calc f θ ^ 2 * (Real.sin θ) ^ (-η)
        ≤ C ^ 2 * θ ^ 2 * (Real.sin θ) ^ (-η) := mul_le_mul_of_nonneg_right (hf2 θ hθ) hw.le
      _ ≤ C ^ 2 * θ ^ 2 * ((Real.pi / 2) ^ η * θ ^ (-η)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C ^ 2 * (Real.pi / 2) ^ η * (θ ^ 2 * θ ^ (-η)) := by ring
      _ ≤ C ^ 2 * (Real.pi / 2) ^ η * ((Real.pi / 2) ^ 2 * θ ^ (-η)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hθ2le (Real.rpow_nonneg hθ.1.le _)) (by positivity)
      _ = C ^ 2 * (Real.pi / 2) ^ η * (Real.pi / 2) ^ 2 * θ ^ (-η) := by ring

/-! ## The weighted `L²` bound `∫ f² sin^{-η} ≤ K ∫ f'²` on `[0, π/2]` -/

private theorem sin_l2_weight_bound_pi2 {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 →
      (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η))
        ≤ K * (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv f θ) ^ 2) := by
  obtain ⟨K0, hK0pos, hK0⟩ := sin_l2_weight_bound (η := η) hη0 hη1
  have hP : (0 : ℝ) < Real.pi / 2 := by positivity
  refine ⟨2 ^ η * K0, mul_pos (by positivity) hK0pos, fun f hf h0 => ?_⟩
  have hIcc : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (Real.pi / 2))), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Measure.restrict_congr_set
      (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm]
    exact self_mem_ae_restrict measurableSet_Ioo
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn.pow 2)
  have hint2 : IntegrableOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Icc 0 (Real.pi / 2)) volume := by
    have hmaj : IntegrableOn (fun θ => Cf * (Real.sin (2 * θ)) ^ (-η))
        (Set.Icc 0 (Real.pi / 2)) volume :=
      (Work.Spaces.sin_two_rpow (-η) (by linarith) (by linarith)).1.const_mul Cf
    refine Integrable.mono' hmaj ?_ ?_
    · exact ((hf.continuousOn.pow 2).aestronglyMeasurable measurableSet_Icc).mul
        (((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const (-η))
          |>.aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hsin2 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hsin2 _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw)]
      have hb : f θ ^ 2 ≤ Cf := by
        simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f θ))] using hCf θ hθ
      exact mul_le_mul_of_nonneg_right hb hw
  have hpoint : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (Real.pi / 2))),
      f θ ^ 2 * (Real.sin θ) ^ (-η) ≤ 2 ^ η * (f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
    filter_upwards [hIcc] with θ hθ
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hsin2 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hle : Real.sin (2 * θ) ≤ 2 * Real.sin θ := by
      rw [Real.sin_two_mul]; nlinarith [Real.cos_le_one θ, hsin]
    have h1 : (2 * Real.sin θ) ^ (-η) ≤ (Real.sin (2 * θ)) ^ (-η) :=
      Real.rpow_le_rpow_of_nonpos hsin2 hle (by linarith : -η ≤ 0)
    have h2 : (2 * Real.sin θ) ^ (-η) = 2 ^ (-η) * (Real.sin θ) ^ (-η) :=
      Real.mul_rpow (by norm_num) hsin.le
    rw [h2] at h1
    have h4 : (2 : ℝ) ^ η * 2 ^ (-η) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
    have h3 : (Real.sin θ) ^ (-η) ≤ 2 ^ η * (Real.sin (2 * θ)) ^ (-η) := by
      calc (Real.sin θ) ^ (-η) = 1 * (Real.sin θ) ^ (-η) := by ring
        _ = (2 ^ η * 2 ^ (-η)) * (Real.sin θ) ^ (-η) := by rw [h4]
        _ = 2 ^ η * (2 ^ (-η) * (Real.sin θ) ^ (-η)) := by ring
        _ ≤ 2 ^ η * (Real.sin (2 * θ)) ^ (-η) := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc f θ ^ 2 * (Real.sin θ) ^ (-η) ≤ f θ ^ 2 * (2 ^ η * (Real.sin (2 * θ)) ^ (-η)) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = 2 ^ η * (f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by ring
  have hstep : (∫ θ in Set.Icc 0 (Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η))
      ≤ ∫ θ in Set.Icc 0 (Real.pi / 2), 2 ^ η * (f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) :=
    MeasureTheory.integral_mono_of_nonneg
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
            by linarith [hθ.2, Real.pi_pos]⟩) _))
      (hint2.const_mul (2 ^ η)) hpoint
  rw [MeasureTheory.integral_const_mul] at hstep
  rw [integral_Icc_eq_interval hP.le (fun θ => f θ ^ 2 * (Real.sin θ) ^ (-η)),
      integral_Icc_eq_interval hP.le (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))] at hstep
  have hmain : (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      ≤ K0 * (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv f θ) ^ 2) := by
    have h := hK0 f hf h0
    rw [integral_Icc_eq_interval hP.le (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)),
        integral_Icc_eq_interval hP.le (fun θ => (deriv f θ) ^ 2)] at h
    exact h
  calc (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η))
      ≤ 2 ^ η * (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := hstep
    _ ≤ 2 ^ η * (K0 * (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv f θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (2 ^ η * K0) * (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv f θ) ^ 2) := by ring

/-! ## Reflection of interval integrability across `π/2 ↦ π` -/

private lemma intervalIntegrable_reflect {F : ℝ → ℝ}
    (h : IntervalIntegrable (fun u => F (Real.pi - u)) volume 0 (Real.pi / 2)) :
    IntervalIntegrable F volume (Real.pi / 2) Real.pi := by
  have hc : IntervalIntegrable (fun x => F (Real.pi - (Real.pi - x))) volume
      (Real.pi - 0) (Real.pi - Real.pi / 2) := h.comp_sub_left Real.pi
  rw [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at hc
  have heq : (fun x => F (Real.pi - (Real.pi - x))) = F := by
    funext x; rw [sub_sub_cancel]
  rw [heq] at hc
  rw [intervalIntegrable_iff] at hc ⊢
  rwa [uIoc_comm (Real.pi / 2) Real.pi]

/-! ## The main theorem -/

theorem sharp_hardy_pi (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 π) → f 0 = 0 → f π = 0 →
      (∫ θ in Set.Icc 0 π, f θ ^ 2 / (Real.sin θ) ^ (2 + η))
        ≤ 4 / (η + 1) ^ 2 * (∫ θ in Set.Icc 0 π, (deriv f θ) ^ 2 / (Real.sin θ) ^ η)
          + C * ((∫ θ in Set.Icc 0 π, f θ ^ 2) + ∫ θ in Set.Icc 0 π, (deriv f θ) ^ 2) := by
  obtain ⟨C0, hC0pos, hhalf⟩ := half_pi_sin_hardy (η := η) hη0 hη1
  obtain ⟨K, hKpos, hKb⟩ := sin_l2_weight_bound_pi2 (η := η) hη0 hη1
  have hP : (0 : ℝ) < Real.pi / 2 := by positivity
  refine ⟨C0 * K, mul_pos hC0pos hKpos, fun f hf hf0 hfπ => ?_⟩
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsub2 : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 Real.pi :=
    Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hf' : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) := hf.mono hsub2
  have hrefl : ContDiffOn ℝ 1 (fun u : ℝ => f (Real.pi - u)) (Set.Icc 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (fun u : ℝ => Real.pi - u) (Set.Icc 0 (Real.pi / 2)) := by fun_prop
    have hmaps : Set.MapsTo (fun u : ℝ => Real.pi - u) (Set.Icc 0 (Real.pi / 2))
        (Set.Icc 0 Real.pi) := by
      intro u hu
      simp only [Set.mem_Icc] at hu ⊢
      exact ⟨by linarith [hu.2, Real.pi_pos], by linarith [hu.1]⟩
    have h2 := hf.comp h1 hmaps
    simpa [Function.comp_def] using h2
  have hrefl0 : (fun u : ℝ => f (Real.pi - u)) 0 = 0 := by simpa using hfπ
  -- the two half-inequalities
  have hL := hhalf f hf' hf0
  have hRraw := hhalf (fun u : ℝ => f (Real.pi - u)) hrefl hrefl0
  -- integrability on `[0, π/2]`
  have hIntL := intervalIntegrable_pi2_three (η := η) hη0 hη1 hf' hf0
  have hIntR := intervalIntegrable_pi2_three (η := η) hη0 hη1 hrefl hrefl0
  -- the reflection identities
  have hc1 : (∫ u in (0 : ℝ)..(Real.pi / 2), f (Real.pi - u) ^ 2 * (Real.sin u) ^ (-(2 + η)))
      = ∫ θ in (Real.pi / 2)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := fun θ : ℝ => f θ ^ 2 * (Real.sin θ) ^ (-(2 + η))) Real.pi
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [Real.sin_pi_sub]
  have hc2 : (∫ u in (0 : ℝ)..(Real.pi / 2),
        (deriv (fun u : ℝ => f (Real.pi - u)) u) ^ 2 * (Real.sin u) ^ (-η))
      = ∫ θ in (Real.pi / 2)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η)) Real.pi
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [deriv_comp_const_sub, neg_sq, Real.sin_pi_sub]
  have hc3 : (∫ u in (0 : ℝ)..(Real.pi / 2), f (Real.pi - u) ^ 2 * (Real.sin u) ^ (-η))
      = ∫ θ in (Real.pi / 2)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-η) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := fun θ : ℝ => f θ ^ 2 * (Real.sin θ) ^ (-η)) Real.pi
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [Real.sin_pi_sub]
  have hcderiv : (∫ u in (0 : ℝ)..(Real.pi / 2), (deriv (fun u : ℝ => f (Real.pi - u)) u) ^ 2)
      = ∫ θ in (Real.pi / 2)..Real.pi, (deriv f θ) ^ 2 := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi / 2) (f := fun θ : ℝ => (deriv f θ) ^ 2) Real.pi
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [deriv_comp_const_sub, neg_sq]
  -- the right half bound as a statement about `f` on `[π/2, π]`
  have hR : (∫ θ in (Real.pi / 2)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * (∫ θ in (Real.pi / 2)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
        + C0 * (∫ θ in (Real.pi / 2)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-η)) := by
    rw [← hc1, ← hc2, ← hc3]; exact hRraw
  -- integrability on `[π/2, π]` by reflection
  have hIntF1R : IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
      volume (Real.pi / 2) Real.pi :=
    intervalIntegrable_reflect (by simpa only [Real.sin_pi_sub] using hIntR.1)
  have hIntF2R : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
      volume (Real.pi / 2) Real.pi :=
    intervalIntegrable_reflect (by simpa only [Real.sin_pi_sub, deriv_comp_const_sub, neg_sq] using hIntR.2.1)
  have hIntF3R : IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin θ) ^ (-η))
      volume (Real.pi / 2) Real.pi :=
    intervalIntegrable_reflect (by simpa only [Real.sin_pi_sub] using hIntR.2.2)
  -- combine the two halves
  have e1 := intervalIntegral.integral_add_adjacent_intervals hIntL.1 hIntF1R
  have e2 := intervalIntegral.integral_add_adjacent_intervals hIntL.2.1 hIntF2R
  have e3 := intervalIntegral.integral_add_adjacent_intervals hIntL.2.2 hIntF3R
  have hkey : (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
        + C0 * (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-η)) := by
    calc (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
        = (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
          + (∫ θ in (Real.pi / 2)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-(2 + η))) := e1.symm
      _ ≤ (4 / (1 + η) ^ 2 * (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
            + C0 * (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η)))
          + (4 / (1 + η) ^ 2 * (∫ θ in (Real.pi / 2)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
            + C0 * (∫ θ in (Real.pi / 2)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-η))) :=
          add_le_add hL hR
      _ = 4 / (1 + η) ^ 2 * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
          + C0 * (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-η)) := by
          rw [← e2, ← e3]; ring
  -- the `L²` weight term
  have hIntD : IntervalIntegrable (fun θ => (deriv f θ) ^ 2) volume 0 Real.pi := by
    obtain ⟨Cd, hCd0, _, hbd⟩ := power_hardy_bounds Real.pi_pos hf hf0
    have hdc : ContinuousOn (deriv f) (Set.Ioo 0 Real.pi) := by
      have h1 : ContinuousOn (fun t => derivWithin f (Set.Icc 0 Real.pi) t) (Set.Ioo 0 Real.pi) :=
        (hf.continuousOn_derivWithin (uniqueDiffOn_Icc Real.pi_pos) le_rfl).mono
          Set.Ioo_subset_Icc_self
      refine h1.congr (fun t ht => ?_)
      exact (derivWithin_of_mem_nhds
        (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)).symm
    refine intervalIntegrable_of_continuousOn_Ioo_of_bound Real.pi_pos.le (hdc.pow 2) (Cd ^ 2)
      (fun t ht => ?_)
    rw [abs_of_nonneg (sq_nonneg _), sq_le_sq, abs_of_nonneg hCd0]
    exact hbd t ht
  have hDhalf1 : IntervalIntegrable (fun θ => (deriv f θ) ^ 2) volume 0 (Real.pi / 2) :=
    hIntD.mono_set (by
      rw [Set.uIcc_of_le hP.le, Set.uIcc_of_le hπpos.le]
      exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
  have hDhalf2 : IntervalIntegrable (fun θ => (deriv f θ) ^ 2) volume (Real.pi / 2) Real.pi :=
    hIntD.mono_set (by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (Real.pi / 2) ≤ Real.pi), Set.uIcc_of_le hπpos.le]
      exact Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)
  have ederiv := intervalIntegral.integral_add_adjacent_intervals hDhalf1 hDhalf2
  have hW : (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-η))
      ≤ K * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2) := by
    have hWl := hKb f hf' hf0
    have hWr := hKb (fun u : ℝ => f (Real.pi - u)) hrefl hrefl0
    rw [hc3, hcderiv] at hWr
    calc (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-η))
        = (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η))
          + (∫ θ in (Real.pi / 2)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-η)) := e3.symm
      _ ≤ K * (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv f θ) ^ 2)
          + K * (∫ θ in (Real.pi / 2)..Real.pi, (deriv f θ) ^ 2) := add_le_add hWl hWr
      _ = K * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2) := by rw [← ederiv]; ring
  -- assemble
  have hfin : (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
        + C0 * K * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hW hC0pos.le
    linarith [hkey]
  have hDnn : 0 ≤ ∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 :=
    intervalIntegral.integral_nonneg hπpos.le (fun θ _ => sq_nonneg _)
  -- convert to set integrals over `Icc 0 π`
  have hLHS : (∫ θ in Set.Icc 0 π, f θ ^ 2 / (Real.sin θ) ^ (2 + η))
      = ∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)) := by
    rw [integral_Icc_eq_interval hπpos.le]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hπpos.le] at hθ
    show f θ ^ 2 / (Real.sin θ) ^ (2 + η) = f θ ^ 2 * (Real.sin θ) ^ (-(2 + η))
    rw [div_eq_mul_inv, Real.rpow_neg (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2⟩) (2 + η)]
  have hRHS1 : (∫ θ in Set.Icc 0 π, (deriv f θ) ^ 2 / (Real.sin θ) ^ η)
      = ∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η) := by
    rw [integral_Icc_eq_interval hπpos.le]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hπpos.le] at hθ
    show (deriv f θ) ^ 2 / (Real.sin θ) ^ η = (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η)
    rw [div_eq_mul_inv, Real.rpow_neg (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2⟩) η]
  have hRHS2 : (∫ θ in Set.Icc 0 π, (deriv f θ) ^ 2)
      = ∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 :=
    integral_Icc_eq_interval hπpos.le (fun θ => (deriv f θ) ^ 2)
  have hRHSf : (∫ θ in Set.Icc 0 π, f θ ^ 2) = ∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 :=
    integral_Icc_eq_interval hπpos.le (fun θ => f θ ^ 2)
  have hDnnI : 0 ≤ ∫ θ in Set.Icc 0 π, f θ ^ 2 := by
    rw [hRHSf]; exact intervalIntegral.integral_nonneg hπpos.le (fun θ _ => sq_nonneg _)
  rw [hLHS, hRHS1, hRHS2, hRHSf]
  have hcoef : (4:ℝ) / (η + 1) ^ 2 = 4 / (1 + η) ^ 2 := by ring_nf
  rw [hcoef]
  calc (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
        + C0 * K * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2) := hfin
    _ ≤ 4 / (1 + η) ^ 2 * (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
        + C0 * K * ((∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2)
            + ∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2) := by
        have hInn : (0 : ℝ) ≤ ∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 :=
          intervalIntegral.integral_nonneg hπpos.le (fun θ _ => sq_nonneg (f θ))
        have hDle : (∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2)
            ≤ (∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2) + ∫ θ in (0 : ℝ)..Real.pi, (deriv f θ) ^ 2 := by
          linarith [hInn]
        have hmul := mul_le_mul_of_nonneg_left hDle (mul_nonneg hC0pos.le hKpos.le)
        linarith [hmul]

end Work.Elliptic
