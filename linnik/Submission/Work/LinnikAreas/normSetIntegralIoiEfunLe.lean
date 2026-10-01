import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open MeasureTheory

/-- Tail bound for the error term `E(t) = A(t) - t·L(1,χ)`.

If `‖E(t)‖ ≤ K √t` for all `t ≥ 1`, then for `β > 1/2` and `x ≥ 1` the improper
integral `∫_x^∞ E(t) t^{-(β+1)} dt` is bounded by the corresponding integral of the
majorant `K t^{1/2} · t^{-(β+1)} = K t^{-(β+1/2)}`, whose value is
`K x^{1/2-β}/(β - 1/2)`. -/
theorem normSetIntegralIoiEfunLe {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {K β : ℝ} (hK : 0 ≤ K)
    (hE : ∀ t : ℝ, 1 ≤ t → ‖Work.LinnikAreas.Efun χ t‖ ≤ K * Real.sqrt t)
    (hβ : 1/2 < β) {x : ℝ} (hx : 1 ≤ x) :
    ‖∫ t in Set.Ioi x, Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1))‖
      ≤ K * x ^ (1/2 - β) / (β - 1/2) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  set f : ℝ → ℂ := fun t => Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1)) with hf
  have hr : -β - 1/2 < (-1 : ℝ) := by linarith
  -- the majorant is integrable on `Ioi x`
  have hbnd_int : IntegrableOn (fun t : ℝ => K * t ^ (-β - 1/2)) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt hr hx0).const_mul K
  -- and its integral is exactly the claimed bound
  have hval : ∫ t in Set.Ioi x, K * t ^ (-β - 1/2) = K * x ^ (1 / 2 - β) / (β - 1 / 2) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hr hx0]
    rw [show (-β - 1 / 2 + 1 : ℝ) = 1 / 2 - β by ring]
    rw [show (1 / 2 - β : ℝ) = -(β - 1 / 2) by ring]
    rw [neg_div_neg_eq, mul_div_assoc]
  -- pointwise domination of the integrand by the majorant
  have hpoint : ∀ t ∈ Set.Ioi x, ‖f t‖ ≤ K * t ^ (-β - 1/2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hx ht)
    calc ‖f t‖ = ‖Work.LinnikAreas.Efun χ t * (t : ℂ) ^ (-((β : ℂ) + 1))‖ := rfl
      _ = ‖Work.LinnikAreas.Efun χ t‖ * ‖(t : ℂ) ^ (-((β : ℂ) + 1))‖ := norm_mul _ _
      _ = ‖Work.LinnikAreas.Efun χ t‖ * t ^ (-(β + 1)) := by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]; simp
      _ ≤ (K * Real.sqrt t) * t ^ (-(β + 1)) := by
            exact mul_le_mul_of_nonneg_right (hE t ht1) (Real.rpow_nonneg (le_of_lt ht0) _)
      _ = K * t ^ (-β - 1/2) := by
            have he : (1/2 : ℝ) + (-(β + 1)) = -β - 1/2 := by ring
            rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add ht0, he]
  by_cases hInt : IntegrableOn f (Set.Ioi x)
  · -- integrable case: bound the norm of the integral by the integral of the majorant
    have hmono : ∫ t in Set.Ioi x, ‖f t‖ ≤ ∫ t in Set.Ioi x, K * t ^ (-β - 1/2) :=
      MeasureTheory.setIntegral_mono_on hInt.norm hbnd_int measurableSet_Ioi hpoint
    have hnorm := MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi x)) f
    rw [← hval]
    calc ‖∫ t in Set.Ioi x, f t‖ ≤ ∫ t in Set.Ioi x, ‖f t‖ := hnorm
      _ ≤ ∫ t in Set.Ioi x, K * t ^ (-β - 1/2) := hmono
  · -- non-integrable case: the integral is zero
    rw [MeasureTheory.integral_undef hInt]
    simp only [norm_zero]
    exact div_nonneg (mul_nonneg hK (Real.rpow_nonneg (le_of_lt hx0) _)) (by linarith)

end Work.LinnikAreas
