import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.EllExist.Honesty.G1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set

namespace Work.FTS.EllExist.Honesty

-- Far-field pointwise bound for the `z^{s⁻}` Green term `G1 α m c`
-- (`s⁻ = -(2m+5)/α`) of `Work.FTS.EllExist.Honesty.G1`, defined as
-- `G1 α m c z = z ^ (-(2*(m:ℝ)+5)/α) * ∫ t in (0:ℝ)..z, c t * t ^ ((2*(m:ℝ)+5)/α - 1)`.
-- Route: `a := (2*(m:ℝ)+5)/α`, `b := 2*(m:ℝ)/α`, `f t := c t * t ^ (a - 1)`, note
-- `a - b = 5/α ≥ 20` (from `hα4` and `hα`), and case-split on
-- `Good := MeasureTheory.IntegrableOn f (Set.Icc 0 1)`.
-- * If `Good`: for `z ≥ 1` the integrand `f` is continuous on `Icc 1 z ⊆ Set.Ioi 0`, so
--   `intervalIntegral.integral_add_adjacent_intervals` splits `∫_0^z = ∫_0^1 + ∫_1^z`; the
--   second piece is `≤ M * ∫_1^z t ^ (a - b - 3) ≤ M * z ^ (a - b - 2) / (a - b - 2)` using
--   `hdec`, monotonicity of the integral and `integral_rpow` (the exponent `a - b - 3` is
--   `> -1`), while `∫_0^1 f` is a fixed real.  Multiply by `z ^ (-a)` (`Real.rpow_add`).
-- * If `¬ Good` then `f` is not interval integrable on `0..z` for any `z ≥ 1` (otherwise
--   `MeasureTheory.IntegrableOn.mono_set` would give `Good`), so
--   `intervalIntegral.integral_undef` makes `G1 α m c z = 0` there; take `A = B = 0`.
theorem G1_far_bound (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ} (M : ℝ)
    (hM : 0 ≤ M) (hc : ContinuousOn c (Set.Ioi 0))
    (hdec : ∀ t, 1 ≤ t → |c t| ≤ M * t ^ (-(2 * (m : ℝ) / α) - 2)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ Set.Ioi 1,
      |Work.FTS.EllExist.Honesty.G1 α m c z|
        ≤ A * z ^ (-((2 * (m : ℝ) + 5) / α))
          + B * z ^ (-(2 * (m : ℝ) / α) - 2) := by
  -- Write `a = (2m+5)/α`, `b = 2m/α`; the crucial numerical input is `a - b = 5/α ≥ 20`
  -- (from `hα` and `hα4`), which makes the far-field exponent `a - b - 3` nonnegative.
  set a : ℝ := (2 * (m : ℝ) + 5) / α with ha
  set b : ℝ := 2 * (m : ℝ) / α with hb
  have h5 : (20 : ℝ) ≤ 5 / α := by
    have h4 : (4 : ℝ) ≤ 1 / α := by
      rw [le_div_iff₀ hα]; linarith
    have h5e : 5 / α = 5 * (1 / α) := by ring
    rw [h5e]; linarith
  have hab : a - b = 5 / α := by rw [ha, hb]; ring
  have he0 : (0 : ℝ) ≤ a - b - 3 := by linarith
  -- `G1` in terms of `a` and the integrand `t ↦ c t · t^{a-1}`.
  have hG1 : ∀ z, G1 α m c z = z ^ (-a) * (∫ t in (0 : ℝ)..z, c t * t ^ (a - 1)) := by
    intro z
    rw [show G1 α m c z = z ^ ((-(2 * (m : ℝ) + 5)) / α)
        * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) from rfl]
    rw [show (-(2 * (m : ℝ) + 5)) / α = -a by rw [ha]; ring]
  have hcont : ContinuousOn (fun t : ℝ => c t * t ^ (a - 1)) (Set.Ioi 0) :=
    hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  by_cases hGood : IntegrableOn (fun t : ℝ => c t * t ^ (a - 1)) (Set.Ioc 0 1)
  · -- The integrable case: `A = |∫_0^1 f|` and `B = M`.
    refine ⟨|∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)|, M, abs_nonneg _, hM, fun z hz => ?_⟩
    have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
    have hz0 : (0 : ℝ) < z := lt_trans zero_lt_one hz
    have hI01 : IntervalIntegrable (fun t : ℝ => c t * t ^ (a - 1)) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2 hGood
    have hI1z : IntervalIntegrable (fun t : ℝ => c t * t ^ (a - 1)) volume 1 z := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz1]
      exact ((hcont.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1)).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have hsplit : (∫ t in (0 : ℝ)..z, c t * t ^ (a - 1))
        = (∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)) + (∫ t in (1 : ℝ)..z, c t * t ^ (a - 1)) :=
      (intervalIntegral.integral_add_adjacent_intervals hI01 hI1z).symm
    -- The far piece is bounded by `M · z^{a-b-2}`.
    have hb2 : |∫ t in (1 : ℝ)..z, c t * t ^ (a - 1)| ≤ M * z ^ (a - b - 2) := by
      have h1 : |∫ t in (1 : ℝ)..z, c t * t ^ (a - 1)|
          ≤ ∫ t in (1 : ℝ)..z, |c t * t ^ (a - 1)| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun t : ℝ => c t * t ^ (a - 1)) hz1
      have h2 : ∫ t in (1 : ℝ)..z, |c t * t ^ (a - 1)|
          ≤ ∫ t in (1 : ℝ)..z, M * z ^ (a - b - 3) := by
        refine intervalIntegral.integral_mono_on hz1 hI1z.abs intervalIntegrable_const ?_
        intro x hx
        have hx1 : (1 : ℝ) ≤ x := hx.1
        have hxz : x ≤ z := hx.2
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
        have hcx : |c x| ≤ M * x ^ (-b - 2) := hdec x hx1
        have hxa : (0 : ℝ) ≤ x ^ (a - 1) := Real.rpow_nonneg (le_of_lt hx0) _
        have hxe : x ^ (-b - 2) * x ^ (a - 1) = x ^ (a - b - 3) := by
          rw [← Real.rpow_add hx0]; congr 1; ring
        calc |c x * x ^ (a - 1)| = |c x| * x ^ (a - 1) := by rw [abs_mul, abs_of_nonneg hxa]
          _ ≤ (M * x ^ (-b - 2)) * x ^ (a - 1) := mul_le_mul_of_nonneg_right hcx hxa
          _ = M * x ^ (a - b - 3) := by rw [mul_assoc, hxe]
          _ ≤ M * z ^ (a - b - 3) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt hx0) hxz he0) hM
      have h3 : ∫ t in (1 : ℝ)..z, M * z ^ (a - b - 3) = M * z ^ (a - b - 3) * (z - 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      have h4 : M * z ^ (a - b - 3) * (z - 1) ≤ M * z ^ (a - b - 2) := by
        have hze : (0 : ℝ) ≤ z ^ (a - b - 3) := Real.rpow_nonneg (le_of_lt hz0) _
        have hzm : (0 : ℝ) ≤ M * z ^ (a - b - 3) := mul_nonneg hM hze
        have h41 : M * z ^ (a - b - 3) * (z - 1) ≤ M * z ^ (a - b - 3) * z :=
          mul_le_mul_of_nonneg_left (by linarith) hzm
        have h42 : z ^ (a - b - 3) * z = z ^ (a - b - 2) := by
          rw [show a - b - 2 = (a - b - 3) + 1 by ring, Real.rpow_add hz0, Real.rpow_one]
        have h43 : M * z ^ (a - b - 3) * z = M * z ^ (a - b - 2) := by rw [mul_assoc, h42]
        linarith
      linarith
    have hbnd : |∫ t in (0 : ℝ)..z, c t * t ^ (a - 1)|
        ≤ |∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)| + M * z ^ (a - b - 2) := by
      rw [hsplit]
      calc |(∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)) + (∫ t in (1 : ℝ)..z, c t * t ^ (a - 1))|
          ≤ |∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)| + |∫ t in (1 : ℝ)..z, c t * t ^ (a - 1)| :=
            abs_add_le _ _
        _ ≤ |∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)| + M * z ^ (a - b - 2) := by linarith
    have hza : (0 : ℝ) ≤ z ^ (-a) := Real.rpow_nonneg (le_of_lt hz0) _
    have hze3 : z ^ (-a) * z ^ (a - b - 2) = z ^ (-b - 2) := by
      rw [← Real.rpow_add hz0]; congr 1; ring
    calc |G1 α m c z| = z ^ (-a) * |∫ t in (0 : ℝ)..z, c t * t ^ (a - 1)| := by
          rw [hG1 z, abs_mul, abs_of_nonneg hza]
      _ ≤ z ^ (-a) * (|∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)| + M * z ^ (a - b - 2)) :=
          mul_le_mul_of_nonneg_left hbnd hza
      _ = |∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)| * z ^ (-a) + M * z ^ (-b - 2) := by
          have e : z ^ (-a) * (|∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)| + M * z ^ (a - b - 2))
              = |∫ t in (0 : ℝ)..1, c t * t ^ (a - 1)| * z ^ (-a)
                + M * (z ^ (-a) * z ^ (a - b - 2)) := by ring
          rw [e, hze3]
  · -- The non-integrable case: the interval integral is `0` by convention, so `A = B = 0`.
    refine ⟨0, 0, le_rfl, le_rfl, fun z hz => ?_⟩
    have hz0 : (0 : ℝ) ≤ z := le_of_lt (lt_trans zero_lt_one hz)
    have hnot : ¬ IntervalIntegrable (fun t : ℝ => c t * t ^ (a - 1)) volume 0 z := by
      intro hInt
      apply hGood
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ z from hz0)] at hInt
      exact hInt.mono_set (fun x hx => ⟨hx.1, le_trans hx.2 (le_of_lt hz)⟩)
    have hzero : G1 α m c z = 0 := by
      rw [hG1 z, intervalIntegral.integral_undef hnot, mul_zero]
    rw [hzero]
    simp

end Work.FTS.EllExist.Honesty
