import Mathlib
open MeasureTheory

namespace Work.JR

theorem abel_change_of_variables {D : ℝ} (hD : 1 < D) {s T : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {f : ℝ → ℝ} (hf : IntervalIntegrable (fun t : ℝ => f (D ^ (1 / t))) volume s T) :
    (∫ u in D ^ (1 / T)..D ^ (1 / s), f u * (Real.log (D ^ (1 / s)) / (u * (Real.log u) ^ 2)))
      = (1 / s) * ∫ t in s..T, f (D ^ (1 / t)) := by
  have hD0 : (0:ℝ) < D := lt_trans zero_lt_one hD
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hderiv0 : ∀ x ≠ 0, HasDerivAt (fun t : ℝ => D ^ (1/t)) (-(D ^ (1/x) * Real.log D / x^2)) x := by
    intro x hx
    have hd1 : HasDerivAt (fun t : ℝ => t⁻¹) (-1/x^2) x := (hasDerivAt_id x).inv hx
    have hd : HasDerivAt (fun t : ℝ => Real.log D * t⁻¹) (Real.log D * (-1/x^2)) x :=
      HasDerivAt.const_mul (Real.log D) hd1
    have hE : HasDerivAt (fun t : ℝ => Real.exp (Real.log D * t⁻¹))
        (Real.exp (Real.log D * x⁻¹) * (Real.log D * (-1/x^2))) x := hd.exp
    have hval : Real.exp (Real.log D * x⁻¹) * (Real.log D * (-1/x^2))
        = -(D ^ (1/x) * Real.log D / x^2) := by
      rw [show Real.exp (Real.log D * x⁻¹) = D^(1/x) from by
          rw [Real.rpow_def_of_pos hD0]; simp only [one_div]]
      ring
    rw [hval] at hE
    refine hE.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Real.rpow_def_of_pos hD0, one_div])
  have hderiv : ∀ x ∈ Set.Ioo s T,
      HasDerivAt (fun t : ℝ => D ^ (1/t)) (-(D ^ (1/x) * Real.log D / x^2)) x :=
    fun x hx => hderiv0 x (ne_of_gt (lt_of_lt_of_le hs hx.1.le))
  have hcont : ContinuousOn (fun t : ℝ => D ^ (1/t)) (Set.Icc s T) :=
    HasDerivAt.continuousOn (fun x hx => hderiv0 x (ne_of_gt (lt_of_lt_of_le hs hx.1)))
  have hnonpos : ∀ x ∈ Set.Ioo s T, (-(D ^ (1/x) * Real.log D / x^2)) ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := lt_trans hs hx.1
    have h1 : 0 < D ^ (1/x) := Real.rpow_pos_of_pos hD0 _
    have h3 : 0 < D ^ (1/x) * Real.log D / x^2 := div_pos (mul_pos h1 hlogD) (pow_pos hx0 2)
    exact neg_nonpos.mpr h3.le
  have key := MeasureTheory.integral_Icc_deriv_smul_of_deriv_nonpos
    (f := fun t : ℝ => D ^ (1/t))
    (f' := fun t : ℝ => -(D ^ (1/t) * Real.log D / t^2))
    (g := fun u : ℝ => f u * (Real.log D / (u * (Real.log u) ^ 2)))
    hcont hderiv hnonpos hsT
  have hpt : ∀ x ∈ Set.Icc s T,
      (-(D ^ (1/x) * Real.log D / x^2))
        • (f (D ^ (1/x)) * (Real.log D / (D ^ (1/x) * (Real.log (D ^ (1/x))) ^ 2)))
        = -(f (D ^ (1/x))) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
    have hA : D ^ (1/x) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hD0 _)
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hL : Real.log D ≠ 0 := ne_of_gt hlogD
    have hlogphi : Real.log (D ^ (1/x)) = Real.log D / x := by
      rw [Real.log_rpow hD0]; ring
    rw [smul_eq_mul, hlogphi]
    field_simp
  have hLHS : (∫ x in Set.Icc s T, (-(D ^ (1/x) * Real.log D / x^2))
        • (f (D ^ (1/x)) * (Real.log D / (D ^ (1/x) * (Real.log (D ^ (1/x))) ^ 2))))
      = -∫ x in Set.Icc s T, f (D ^ (1/x)) := by
    rw [show (∫ x in Set.Icc s T, (-(D ^ (1/x) * Real.log D / x^2))
          • (f (D ^ (1/x)) * (Real.log D / (D ^ (1/x) * (Real.log (D ^ (1/x))) ^ 2))))
          = ∫ x in Set.Icc s T, -(f (D ^ (1/x))) from by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact hpt x hx]
    rw [MeasureTheory.integral_neg]
  have hmain : (∫ x in Set.Icc s T, f (D ^ (1/x)))
      = ∫ u in Set.Icc (D^(1/T)) (D^(1/s)), f u * (Real.log D / (u * (Real.log u)^2)) := by
    rw [hLHS] at key
    exact neg_injective key
  have hconv1 : (∫ x in Set.Icc s T, f (D ^ (1/x))) = ∫ t in s..T, f (D ^ (1/t)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsT]
  have hle : D ^ (1/T) ≤ D ^ (1/s) := by
    rw [Real.rpow_le_rpow_left_iff hD]
    exact one_div_le_one_div_of_le hs hsT
  have hconv2 : (∫ u in Set.Icc (D^(1/T)) (D^(1/s)), f u * (Real.log D / (u * (Real.log u)^2)))
      = ∫ u in D^(1/T)..D^(1/s), f u * (Real.log D / (u * (Real.log u)^2)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hmain' : (∫ t in s..T, f (D ^ (1/t)))
      = ∫ u in D^(1/T)..D^(1/s), f u * (Real.log D / (u * (Real.log u)^2)) := by
    rw [← hconv1, hmain, hconv2]
  rw [hmain']
  have hlog : Real.log (D ^ (1/s)) = (1/s) * Real.log D := by rw [Real.log_rpow hD0]
  have hstep : (∫ u in D ^ (1/T)..D ^ (1/s), f u * (Real.log (D ^ (1/s)) / (u * (Real.log u) ^ 2)))
      = ∫ u in D ^ (1/T)..D ^ (1/s), (1/s) * (f u * (Real.log D / (u * (Real.log u)^2))) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [hlog]; ring
  rw [hstep, intervalIntegral.integral_const_mul]

end Work.JR
