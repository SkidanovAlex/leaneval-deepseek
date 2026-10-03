import Mathlib

open MeasureTheory

namespace Work.FIArea2

theorem integral_psi_bound {L U M : ℝ} (hM : 0 < M) (hL : 1 ≤ L) (hLU : L ≤ U) :
    ∫ x in L..U, (1 / (M * Real.sqrt x) + 1 / (x * Real.sqrt x)) ≤ 2 * Real.sqrt U / M + 2 / Real.sqrt L := by
  have hderiv : ∀ x ∈ Set.uIcc L U,
      HasDerivAt (fun y : ℝ => 2 * Real.sqrt y / M - 2 / Real.sqrt y)
        (1 / (M * Real.sqrt x) + 1 / (x * Real.sqrt x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    obtain ⟨hLx, hxU⟩ := Set.mem_Icc.mp hx
    have hxpos : 0 < x := by linarith
    have hxsq : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hxpos).ne'
    have hsq : (Real.sqrt x)^2 = x := Real.sq_sqrt (le_of_lt hxpos)
    have hA0 : HasDerivAt (fun y : ℝ => Real.sqrt y) (1/(2*Real.sqrt x)) x :=
      Real.hasDerivAt_sqrt (ne_of_gt hxpos)
    have hA : HasDerivAt (fun y : ℝ => 2 * Real.sqrt y / M) (1/(M*Real.sqrt x)) x :=
      ((hA0.const_mul 2).div_const M).congr_deriv (by field_simp)
    have hB : HasDerivAt (fun y : ℝ => 2 * (Real.sqrt y)⁻¹) (-(1/(x*Real.sqrt x))) x :=
      ((hA0.inv hxsq).const_mul 2).congr_deriv (by rw [hsq]; field_simp)
    refine ((hA.sub hB).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun y => by simp only [Pi.sub_apply]; ring)
  have hcont : ContinuousOn (fun x : ℝ => 1 / (M * Real.sqrt x) + 1 / (x * Real.sqrt x)) (Set.uIcc L U) := by
    apply ContinuousOn.add
    · apply ContinuousOn.div continuousOn_const
      · exact ContinuousOn.mul continuousOn_const Real.continuous_sqrt.continuousOn
      · intro x hx
        rw [Set.uIcc_of_le hLU] at hx
        obtain ⟨hLx, -⟩ := Set.mem_Icc.mp hx
        have hxpos : 0 < x := by linarith
        exact mul_ne_zero hM.ne' (Real.sqrt_pos.mpr hxpos).ne'
    · apply ContinuousOn.div continuousOn_const
      · exact ContinuousOn.mul continuousOn_id Real.continuous_sqrt.continuousOn
      · intro x hx
        rw [Set.uIcc_of_le hLU] at hx
        obtain ⟨hLx, -⟩ := Set.mem_Icc.mp hx
        have hxpos : 0 < x := by linarith
        exact mul_ne_zero hxpos.ne' (Real.sqrt_pos.mpr hxpos).ne'
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (M * Real.sqrt x) + 1 / (x * Real.sqrt x)) volume L U :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : (0:ℝ) ≤ 2 / Real.sqrt U := div_nonneg (by norm_num) (Real.sqrt_nonneg U)
  have h2 : (0:ℝ) ≤ 2 * Real.sqrt L / M :=
    div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg L)) hM.le
  linarith

end Work.FIArea2
