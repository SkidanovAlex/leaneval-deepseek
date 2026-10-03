import Mathlib

namespace Work.FIArea6b

open MeasureTheory

/-- The integral over `[a, b]` of the linear interpolation between the value `A` at `a`
and the value `B` at `b` equals `(b - a) * (A + B) / 2` (the trapezoid rule for a
piecewise-linear graph). -/
theorem integral_interp (a b A B : ℝ) (hab : a < b) :
    ∫ x in a..b, (((b - x) * A + (x - a) * B) / (b - a)) = (b - a) * (A + B) / 2 := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have h3 : IntervalIntegrable (fun x : ℝ => (b - x) * A) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => (b - x) * A).intervalIntegrable a b
  have h4 : IntervalIntegrable (fun x : ℝ => (x - a) * B) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => (x - a) * B).intervalIntegrable a b
  have hb : ∫ x in a..b, (b - x) = (b - a) ^ 2 / 2 := by
    rw [show (fun x : ℝ => b - x) = (fun x : ℝ => (fun _ : ℝ => b) x - id x) from rfl]
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable a b)
      (continuous_id.intervalIntegrable a b)]
    simp only [id_eq, intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  have ha : ∫ x in a..b, (x - a) = (b - a) ^ 2 / 2 := by
    rw [show (fun x : ℝ => x - a) = (fun x : ℝ => id x - (fun _ : ℝ => a) x) from rfl]
    rw [intervalIntegral.integral_sub (continuous_id.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)]
    simp only [id_eq, intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  rw [intervalIntegral.integral_div]
  rw [show (fun x : ℝ => (b - x) * A + (x - a) * B)
        = (fun x : ℝ => (fun y => (b - y) * A) x + (fun y => (y - a) * B) x) from rfl]
  rw [intervalIntegral.integral_add h3 h4]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, hb, ha]
  rw [div_eq_iff hne]
  ring

/-- The volume of the region between the two linear interpolations of `(la, lb)` and `(ua, ub)`
over `[a, b]` is the area of the trapezoid `(b - a) * ((ua - la) + (ub - lb)) / 2`. -/
theorem volume_regionBetween_interp (a b la lb ua ub : ℝ) (hab : a < b) (h1 : la ≤ ua) (h2 : lb ≤ ub) :
    MeasureTheory.volume (regionBetween (fun x => ((b - x) * la + (x - a) * lb) / (b - a))
                          (fun x => ((b - x) * ua + (x - a) * ub) / (b - a)) (Set.Icc a b))
      = ENNReal.ofReal ((b - a) * ((ua - la) + (ub - lb)) / 2) := by
  have hab' : (0 : ℝ) < b - a := sub_pos.mpr hab
  set f : ℝ → ℝ := fun x => ((b - x) * la + (x - a) * lb) / (b - a) with hfdef
  set g : ℝ → ℝ := fun x => ((b - x) * ua + (x - a) * ub) / (b - a) with hgdef
  have hfcont : Continuous f := by rw [hfdef]; fun_prop
  have hgcont : Continuous g := by rw [hgdef]; fun_prop
  have hfint : IntegrableOn f (Set.Icc a b) volume :=
    hfcont.continuousOn.integrableOn_compact isCompact_Icc
  have hgint : IntegrableOn g (Set.Icc a b) volume :=
    hgcont.continuousOn.integrableOn_compact isCompact_Icc
  have hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hx
    have hbx : 0 ≤ b - x := by linarith
    have hxa' : 0 ≤ x - a := by linarith
    simp only [hfdef, hgdef]
    rw [div_le_div_iff_of_pos_right hab']
    nlinarith [mul_nonneg hbx (sub_nonneg.mpr h1), mul_nonneg hxa' (sub_nonneg.mpr h2)]
  have hpt : ∫ y in Set.Icc a b, (g - f) y = (b - a) * ((ua - la) + (ub - lb)) / 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hab)]
    have hcongr : Set.EqOn (fun y => (g - f) y)
        (fun y => ((b - y) * (ua - la) + (y - a) * (ub - lb)) / (b - a)) (Set.uIcc a b) := by
      intro y _
      simp only [Pi.sub_apply, hfdef, hgdef]
      rw [div_sub_div_same]
      ring
    rw [intervalIntegral.integral_congr hcongr, integral_interp a b (ua - la) (ub - lb) hab]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [volume_regionBetween_eq_integral hfint hgint measurableSet_Icc hfg]
  rw [hpt]

end Work.FIArea6b
