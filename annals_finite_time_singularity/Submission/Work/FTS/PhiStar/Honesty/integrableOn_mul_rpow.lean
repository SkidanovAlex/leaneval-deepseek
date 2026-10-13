import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- AM–GM in the form used below: `|y| ≤ (y² + 1)/2`. -/
private lemma abs_le_sq_add_one_div_two (y : ℝ) : |y| ≤ (y ^ 2 + 1) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

/-- The elementary power comparison behind the lemma: for `0 < t ≤ 1` and `-2 ≤ r`,
`t ^ r ≤ (t²)⁻¹`. -/
private lemma rpow_le_inv_sq {t r : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hr : -2 ≤ r) :
    t ^ r ≤ (t ^ 2)⁻¹ := by
  calc t ^ r ≤ t ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hr
    _ = (t ^ (2 : ℝ))⁻¹ := Real.rpow_neg ht0.le 2
    _ = (t ^ 2)⁻¹ := by rw [Real.rpow_two]

/-- If `(c t)²/t⁴` is integrable on `(0,1)` then `c t · t^r` is integrable there for every
`r ≥ -2`: on `(0,1)` one has `|c t · t^r| ≤ |c t/t²|`, i.e. `c · t^r` is dominated by the `L²`
function `c/t²`, and `L² ⊆ L¹` on the finite measure space `(0,1)`.  The endpoints `0` and `1`
contribute nothing. -/
theorem integrableOn_mul_rpow {c : ℝ → ℝ} {r : ℝ} (hr : -2 ≤ r)
    (hc : ContinuousOn c (Set.Ioo 0 1))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ r) (Set.Icc 0 1) := by
  -- Work on the open interval first; the endpoints `0` and `1` are null.
  have keyI : MeasureTheory.Integrable (fun t : ℝ => c t * t ^ r)
      (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := by
    -- An integrable dominating function: `(c t)²/t⁴/2 + 1/2`.
    have hg : MeasureTheory.Integrable
        (fun t : ℝ => ((c t) ^ 2 / t ^ 4) / 2 + 1 / 2)
        (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := by
      have h1 : MeasureTheory.Integrable (fun t : ℝ => ((c t) ^ 2 / t ^ 4) / 2)
          (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := hint.integrable.div_const 2
      have h2 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ) / 2)
          (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := MeasureTheory.integrable_const _
      exact h1.add h2
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · -- almost everywhere strong measurability
      have hcont : ContinuousOn (fun t : ℝ => c t * t ^ r) (Set.Ioo 0 1) :=
        hc.mul (by
          intro x hx
          exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx.1))).continuousWithinAt)
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · -- the pointwise bound on `(0,1)`
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Set.mem_Ioo] at ht
      obtain ⟨ht0, ht1⟩ := ht
      have htnn : 0 ≤ t := ht0.le
      have hpownn : 0 ≤ t ^ r := Real.rpow_nonneg htnn r
      have hle : t ^ r ≤ (t ^ 2)⁻¹ := rpow_le_inv_sq ht0 (le_of_lt ht1) hr
      have hA : |c t| * t ^ r ≤ |c t| * (t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hle (abs_nonneg (c t))
      have hB : |c t| * (t ^ 2)⁻¹ = |c t * (t ^ 2)⁻¹| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
      have hC : |c t * (t ^ 2)⁻¹| ≤ ((c t * (t ^ 2)⁻¹) ^ 2 + 1) / 2 :=
        abs_le_sq_add_one_div_two _
      have hD : (c t * (t ^ 2)⁻¹) ^ 2 = (c t) ^ 2 / t ^ 4 := by
        rw [div_eq_mul_inv, mul_pow, inv_pow]
        rw [show (t ^ 2) ^ 2 = t ^ 4 by ring]
      calc
        ‖c t * t ^ r‖ = |c t| * t ^ r := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpownn]
        _ ≤ |c t| * (t ^ 2)⁻¹ := hA
        _ = |c t * (t ^ 2)⁻¹| := hB
        _ ≤ ((c t * (t ^ 2)⁻¹) ^ 2 + 1) / 2 := hC
        _ = ((c t) ^ 2 / t ^ 4) / 2 + 1 / 2 := by rw [hD]; ring
  have key : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ r) (Set.Ioo 0 1) := keyI
  exact MeasureTheory.IntegrableOn.congr_set_ae key
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))).symm

end Work.FTS.PhiStar.Honesty
