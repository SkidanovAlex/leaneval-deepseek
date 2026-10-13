/-
Copyright: work module for the Elgindi finite-time singularity project.

# The sharp weighted Hardy inequality on `[0, π/2]` with the weight `sin θ`

For `0 ≤ η < 1` there is `C > 0` such that every `f : ℝ → ℝ` of class `C¹` on `[0, π/2]`
with `f 0 = 0` satisfies

`∫_0^{π/2} f(θ)² sin(θ)^{-(2+η)} dθ`
  `≤ 4/(1+η)² ∫_0^{π/2} f'(θ)² sin(θ)^{-η} dθ + C ∫_0^{π/2} f(θ)² sin(θ)^{-η} dθ`.

The constant `4/(1+η)²` is the sharp one of the classical weighted Hardy inequality with the
power weight `θ` (`Work.Elliptic.power_hardy`).  Since `sin θ ≥ (2/π) θ` on `[0, π/2]`, the
leading singularities of `sin(θ)^{-(2+η)}` and `θ^{-(2+η)}` agree and the discrepancy is
dominated by the milder singularity `sin(θ)^{-η}` (`Work.Elliptic.sin_pow_compare`), so the
power-weight inequality transfers with the sharp constant intact.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.sin_pow_compare
import Submission.Work.Elliptic.power_hardy
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## Elementary comparisons for `θ ∈ (0, π/2]` -/

/-- `θ / sin θ ≤ π / 2` on `(0, π/2]` (the reverse of Jordan's inequality `sin θ ≥ 2θ/π`). -/
private lemma div_sin_le_pi2 {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2) :
    θ / Real.sin θ ≤ Real.pi / 2 := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθπ, Real.pi_pos])
  rw [div_le_iff₀ hsin]
  have hmul : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0.le hθπ
  calc θ = Real.pi / 2 * (2 / Real.pi * θ) := by field_simp
    _ ≤ Real.pi / 2 * Real.sin θ := mul_le_mul_of_nonneg_left hmul (by positivity)

/-- For `0 ≤ η`, `0 < θ ≤ π/2`:

* `θ² sin θ^{-(2+η)} ≤ (π/2)^{2+η} θ^{-η}`,
* `θ² sin θ^{-η} ≤ (π/2)^{2+η} θ^{-η}`,
* `sin θ^{-η} ≤ (π/2)^η θ^{-η}`,
* `θ² θ^{-(2+η)} = θ^{-η}`.

All four rest on `θ/sin θ ≤ π/2`; the last is the exponent identity `2 - (2+η) = -η`. -/
private lemma sin_rpow_bound {η : ℝ} (hη0 : 0 ≤ η) {θ : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ ≤ Real.pi / 2) :
    θ ^ 2 * (Real.sin θ) ^ (-(2+η)) ≤ (Real.pi/2)^(2+η) * θ^(-η) ∧
    θ ^ 2 * (Real.sin θ) ^ (-η) ≤ (Real.pi/2)^(2+η) * θ^(-η) ∧
    (Real.sin θ) ^ (-η) ≤ (Real.pi/2)^η * θ^(-η) ∧
    θ ^ 2 * θ ^ (-(2+η)) = θ ^ (-η) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθπ, Real.pi_pos])
  have hP : (0:ℝ) < Real.pi / 2 := by positivity
  have hr : θ / Real.sin θ ≤ Real.pi / 2 := div_sin_le_pi2 hθ0 hθπ
  have hr0 : 0 ≤ θ / Real.sin θ := div_nonneg hθ0.le hsin.le
  have hPeq : (Real.pi/2)^(2+η) = (Real.pi/2)^2 * (Real.pi/2)^η := by
    rw [Real.rpow_add hP (2:ℝ) η]; congr 1; exact Real.rpow_natCast (Real.pi/2) 2
  have hsinneg : (Real.sin θ) ^ (-η) = (θ/Real.sin θ)^η * θ^(-η) := by
    rw [Real.div_rpow hθ0.le hsin.le, Real.rpow_neg hsin.le, div_eq_mul_inv]
    have hθm : θ^η * θ^(-η) = 1 := by
      rw [← Real.rpow_add hθ0, show η + -η = 0 by ring, Real.rpow_zero]
    rw [show θ ^ η * (Real.sin θ ^ η)⁻¹ * θ ^ (-η)
          = (θ^η * θ^(-η)) * (Real.sin θ ^ η)⁻¹ by ring, hθm, one_mul]
  have hrepr1 : θ ^ 2 * (Real.sin θ) ^ (-(2+η)) = (θ/Real.sin θ)^(2+η) * θ^(-η) := by
    rw [Real.div_rpow hθ0.le hsin.le, Real.rpow_neg hsin.le, div_eq_mul_inv,
        show (θ:ℝ)^2 = θ ^ (2:ℝ) by exact (Real.rpow_natCast θ 2).symm]
    have hθ2 : θ ^ (2:ℝ) = θ^(2+η) * θ^(-η) := by
      rw [← Real.rpow_add hθ0 (2+η) (-η)]; congr 1; ring
    rw [hθ2]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrepr1]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr0 hr (by linarith))
      (Real.rpow_nonneg hθ0.le _)
  · rw [hsinneg]
    have hb : θ ^ 2 * (θ/Real.sin θ)^η ≤ (Real.pi/2)^2 * (Real.pi/2)^η := by
      refine mul_le_mul ?_ (Real.rpow_le_rpow hr0 hr hη0) (Real.rpow_nonneg hr0 η) (by positivity)
      rw [sq_le_sq, abs_of_nonneg hθ0.le, abs_of_nonneg hP.le]
      exact hθπ
    calc θ ^ 2 * ((θ/Real.sin θ)^η * θ^(-η))
        = (θ ^ 2 * (θ/Real.sin θ)^η) * θ^(-η) := by ring
      _ ≤ ((Real.pi/2)^2 * (Real.pi/2)^η) * θ^(-η) :=
          mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hθ0.le _)
      _ = (Real.pi/2)^(2+η) * θ^(-η) := by rw [hPeq]
  · rw [hsinneg]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr0 hr hη0) (Real.rpow_nonneg hθ0.le _)
  · rw [show (θ:ℝ)^2 = θ ^ (2:ℝ) by exact (Real.rpow_natCast θ 2).symm, ← Real.rpow_add hθ0]
    congr 1; ring

/-! ## Integrability of the five weighted integrands -/

/-- A function continuous on `(0, π/2)` and dominated there by `K · θ^{-η}` (with `0 ≤ η < 1`)
is integrable on `[0, π/2]`. -/
private lemma integrableOn_Icc_of_le_rpow {η K : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hK : 0 ≤ K)
    {g : ℝ → ℝ} (hgc : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ K * θ ^ (-η)) :
    IntegrableOn g (Set.Icc 0 (Real.pi / 2)) volume := by
  refine integrableOn_of_rpow_majorant hη0 hη1 hK hgc (fun θ hθ => ?_)
  have h1 : (0:ℝ) ≤ θ ^ (-η) := Real.rpow_nonneg hθ.1.le _
  have h2 : (0:ℝ) ≤ (Real.pi / 2 - θ) ^ (-η) := Real.rpow_nonneg (by linarith [hθ.2]) _
  calc ‖g θ‖ ≤ K * θ ^ (-η) := hb θ hθ
    _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h2) hK

/-- Interval-integrability version of `integrableOn_Icc_of_le_rpow`. -/
private lemma intervalIntegrable_of_le_rpow {η K : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hK : 0 ≤ K)
    {g : ℝ → ℝ} (hgc : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ K * θ ^ (-η)) :
    IntervalIntegrable g volume 0 (Real.pi / 2) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)).mpr
    ((integrableOn_Icc_of_le_rpow hη0 hη1 hK hgc hb).mono_set Set.Ioc_subset_Icc_self)

/-- For `f` of class `C¹` on `[0, π/2]` with `f 0 = 0` and `0 ≤ η < 1`, each of the five
weighted integrands appearing in `half_pi_sin_hardy` is interval integrable on `[0, π/2]`.
The bounds on `f` and `deriv f` come from `power_hardy_bounds`; the `θ^{-η}` comparison
from `sin_rpow_bound`. -/
private theorem half_pi_sin_integrable_aux {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (hf0 : f 0 = 0) :
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin θ) ^ (-(2 + η))) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin θ) ^ (-η)) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => f θ ^ 2 * θ ^ (-(2 + η))) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η)) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * θ ^ (-η)) volume 0 (Real.pi / 2) := by
  have hP : (0:ℝ) < Real.pi / 2 := by positivity
  obtain ⟨Cb, hCb0, hbf, hbd⟩ := power_hardy_bounds hP hf hf0
  have hfcont : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) :=
    hf.continuousOn.mono Set.Ioo_subset_Icc_self
  have hdcont : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun t => derivWithin f (Set.Icc 0 (Real.pi / 2)) t)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (hf.continuousOn_derivWithin (uniqueDiffOn_Icc hP) le_rfl).mono Set.Ioo_subset_Icc_self
    refine h1.congr (fun t ht => ?_)
    exact (derivWithin_of_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)).symm
  have hsinpos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.sin θ :=
    fun θ hθ => Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hsin_c : ContinuousOn (fun θ => (Real.sin θ) ^ (-(2+η))) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.continuousOn.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hsin_cη : ContinuousOn (fun θ => (Real.sin θ) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_sin.continuousOn.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hth_c : ContinuousOn (fun θ => θ ^ (-(2+η))) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_id.rpow_const (fun θ hθ => Or.inl hθ.1.ne')
  have hth_cη : ContinuousOn (fun θ => θ ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_id.rpow_const (fun θ hθ => Or.inl hθ.1.ne')
  have hf2sq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), f θ ^ 2 ≤ Cb^2 * θ^2 := by
    intro θ hθ
    have h := hbf θ hθ
    calc f θ ^ 2 ≤ (Cb * θ)^2 := by
          rw [sq_le_sq, abs_of_nonneg (mul_nonneg hCb0 hθ.1.le)]; exact h
      _ = Cb^2 * θ^2 := by ring
  have hd2sq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv f θ) ^ 2 ≤ Cb^2 := by
    intro θ hθ
    have h := hbd θ hθ
    rw [sq_le_sq, abs_of_nonneg hCb0]; exact h
  have hKs : 0 ≤ Cb^2 * (Real.pi/2)^(2+η) := by positivity
  have hKsη : 0 ≤ Cb^2 * (Real.pi/2)^η := by positivity
  have hKp : 0 ≤ Cb^2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine intervalIntegrable_of_le_rpow hη0 hη1 hKs ((hfcont.pow 2).mul hsin_c) (fun θ hθ => ?_)
    have hw : 0 < (Real.sin θ)^(-(2+η)) := Real.rpow_pos_of_pos (hsinpos θ hθ) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw.le)]
    calc f θ ^ 2 * (Real.sin θ) ^ (-(2+η))
        ≤ Cb^2 * θ^2 * (Real.sin θ) ^ (-(2+η)) := mul_le_mul_of_nonneg_right (hf2sq θ hθ) hw.le
      _ = Cb^2 * (θ^2 * (Real.sin θ) ^ (-(2+η))) := by ring
      _ ≤ Cb^2 * ((Real.pi/2)^(2+η) * θ^(-η)) :=
          mul_le_mul_of_nonneg_left ((sin_rpow_bound hη0 hθ.1 (le_of_lt hθ.2)).1) (by positivity)
      _ = Cb^2 * (Real.pi/2)^(2+η) * θ^(-η) := by ring
  · refine intervalIntegrable_of_le_rpow hη0 hη1 hKs ((hfcont.pow 2).mul hsin_cη) (fun θ hθ => ?_)
    have hw : 0 < (Real.sin θ)^(-η) := Real.rpow_pos_of_pos (hsinpos θ hθ) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw.le)]
    calc f θ ^ 2 * (Real.sin θ) ^ (-η)
        ≤ Cb^2 * θ^2 * (Real.sin θ) ^ (-η) := mul_le_mul_of_nonneg_right (hf2sq θ hθ) hw.le
      _ = Cb^2 * (θ^2 * (Real.sin θ) ^ (-η)) := by ring
      _ ≤ Cb^2 * ((Real.pi/2)^(2+η) * θ^(-η)) :=
          mul_le_mul_of_nonneg_left ((sin_rpow_bound hη0 hθ.1 (le_of_lt hθ.2)).2.1) (by positivity)
      _ = Cb^2 * (Real.pi/2)^(2+η) * θ^(-η) := by ring
  · refine intervalIntegrable_of_le_rpow hη0 hη1 hKp ((hfcont.pow 2).mul hth_c) (fun θ hθ => ?_)
    have hw : 0 < θ^(-(2+η)) := Real.rpow_pos_of_pos hθ.1 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw.le)]
    calc f θ ^ 2 * θ ^ (-(2+η)) ≤ Cb^2 * θ^2 * θ ^ (-(2+η)) :=
          mul_le_mul_of_nonneg_right (hf2sq θ hθ) hw.le
      _ = Cb^2 * (θ^2 * θ ^ (-(2+η))) := by ring
      _ = Cb^2 * θ^(-η) := by rw [(sin_rpow_bound hη0 hθ.1 (le_of_lt hθ.2)).2.2.2]
  · refine intervalIntegrable_of_le_rpow hη0 hη1 hKsη ((hdcont.pow 2).mul hsin_cη) (fun θ hθ => ?_)
    have hw : 0 < (Real.sin θ)^(-η) := Real.rpow_pos_of_pos (hsinpos θ hθ) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw.le)]
    calc (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η) ≤ Cb^2 * (Real.sin θ) ^ (-η) :=
          mul_le_mul_of_nonneg_right (hd2sq θ hθ) hw.le
      _ ≤ Cb^2 * ((Real.pi/2)^η * θ^(-η)) :=
          mul_le_mul_of_nonneg_left ((sin_rpow_bound hη0 hθ.1 (le_of_lt hθ.2)).2.2.1) (by positivity)
      _ = Cb^2 * (Real.pi/2)^η * θ^(-η) := by ring
  · refine intervalIntegrable_of_le_rpow hη0 hη1 hKp ((hdcont.pow 2).mul hth_cη) (fun θ hθ => ?_)
    have hw : 0 < θ^(-η) := Real.rpow_pos_of_pos hθ.1 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw.le)]
    exact mul_le_mul_of_nonneg_right (hd2sq θ hθ) hw.le

/-! ## The target theorem -/

/-- **Sharp weighted Hardy inequality on `[0, π/2]` with the weight `sin θ`.**

For `0 ≤ η < 1` there is `C > 0` such that every `f : ℝ → ℝ` of class `C¹` on `[0, π/2]`
with `f 0 = 0` satisfies

`∫_0^{π/2} f(θ)² sin(θ)^{-(2+η)} dθ`
  `≤ 4/(1+η)² ∫_0^{π/2} f'(θ)² sin(θ)^{-η} dθ + C ∫_0^{π/2} f(θ)² sin(θ)^{-η} dθ`. -/
theorem half_pi_sin_hardy {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 →
      (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
        ≤ 4 / (1 + η) ^ 2 * (∫ θ in (0:ℝ)..(Real.pi / 2), (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
          + C * (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := sin_pow_compare (η := η) hη0 hη1
  refine ⟨C0, hC0pos, fun f hf hf0 => ?_⟩
  have hle : (0:ℝ) ≤ Real.pi / 2 := by positivity
  obtain ⟨hIL, hIN, hIM, hIQ, hIP⟩ := half_pi_sin_integrable_aux hη0 hη1 f hf hf0
  -- Pointwise: `sin^{-(2+η)} ≤ θ^{-(2+η)} + C₀ sin^{-η}` (sharp Hardy part plus a correction).
  have hpoint : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      f θ ^ 2 * (Real.sin θ) ^ (-(2 + η))
        ≤ f θ ^ 2 * θ ^ (-(2 + η)) + C0 * (f θ ^ 2 * (Real.sin θ) ^ (-η)) := by
    intro θ hθ
    have h1 := hC0 θ hθ.1 (le_of_lt hθ.2)
    have hf2 : 0 ≤ f θ ^ 2 := sq_nonneg _
    have h2 := mul_le_mul_of_nonneg_left h1 hf2
    rw [mul_add] at h2
    nlinarith [h2]
  -- Monotonicity of the integral.
  have hmono : (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
      ≤ ∫ θ in (0:ℝ)..(Real.pi / 2),
          (f θ ^ 2 * θ ^ (-(2 + η)) + C0 * (f θ ^ 2 * (Real.sin θ) ^ (-η))) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hle hIL (hIM.add (hIN.const_mul C0)) hpoint
  have hsplit : (∫ θ in (0:ℝ)..(Real.pi / 2),
          (f θ ^ 2 * θ ^ (-(2 + η)) + C0 * (f θ ^ 2 * (Real.sin θ) ^ (-η))))
      = (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * θ ^ (-(2 + η)))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η)) := by
    rw [intervalIntegral.integral_add hIM (hIN.const_mul C0), intervalIntegral.integral_const_mul]
  -- The sharp power-weight Hardy inequality at `a = π/2`.
  have hpw := power_hardy (a := Real.pi / 2) (by positivity) hη0 hη1 hf hf0
  have hcoef : (0:ℝ) ≤ 4 / (1 + η) ^ 2 := by positivity
  -- `θ^{-η} ≤ sin θ^{-η}` because `sin θ ≤ θ` and `η ≥ 0`.
  have hQP : (∫ θ in (0:ℝ)..(Real.pi / 2), (deriv f θ) ^ 2 * θ ^ (-η))
      ≤ ∫ θ in (0:ℝ)..(Real.pi / 2), (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hle hIP hIQ ?_
    intro θ hθ
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hsle : Real.sin θ ≤ θ := Real.sin_le hθ.1.le
    have hr := Real.rpow_le_rpow_of_nonpos hsin hsle (by linarith : -η ≤ 0)
    exact mul_le_mul_of_nonneg_left hr (sq_nonneg _)
  calc (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-(2 + η)))
      ≤ ∫ θ in (0:ℝ)..(Real.pi / 2),
          (f θ ^ 2 * θ ^ (-(2 + η)) + C0 * (f θ ^ 2 * (Real.sin θ) ^ (-η))) := hmono
    _ = (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * θ ^ (-(2 + η)))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η)) := hsplit
    _ ≤ 4 / (1 + η) ^ 2 * (∫ θ in (0:ℝ)..(Real.pi / 2), (deriv f θ) ^ 2 * θ ^ (-η))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η)) := by
        have h3 := mul_le_mul_of_nonneg_left hpw hcoef
        linarith
    _ ≤ 4 / (1 + η) ^ 2 * (∫ θ in (0:ℝ)..(Real.pi / 2), (deriv f θ) ^ 2 * (Real.sin θ) ^ (-η))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi / 2), f θ ^ 2 * (Real.sin θ) ^ (-η)) := by
        have h3 := mul_le_mul_of_nonneg_left hQP hcoef
        linarith

end Work.Elliptic
