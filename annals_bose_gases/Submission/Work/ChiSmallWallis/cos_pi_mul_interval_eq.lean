import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory intervalIntegral

namespace Work.ChiSmallWallis

/-- For a continuous even function `f`, `∫_{-a}^{a} f = 2 ∫_0^a f`. -/
lemma integral_neg_self_eq_two_mul (f : ℝ → ℝ) (a : ℝ)
    (heven : ∀ x, f (-x) = f x) (hcont : Continuous f) :
    ∫ x in (-a)..a, f x = 2 * ∫ x in (0:ℝ)..a, f x := by
  have h1 : IntervalIntegrable f volume (-a) 0 := hcont.intervalIntegrable _ _
  have h2 : IntervalIntegrable f volume (0:ℝ) a := hcont.intervalIntegrable _ _
  have hadd : (∫ x in (-a)..0, f x) + (∫ x in (0:ℝ)..a, f x) = ∫ x in (-a)..a, f x :=
    integral_add_adjacent_intervals h1 h2
  have hmirror : ∫ x in (-a)..0, f x = ∫ x in (0:ℝ)..a, f x := by
    have hcn : (∫ x in (0:ℝ)..a, f (-x)) = ∫ x in (-a)..0, f x := by
      simpa only [neg_zero] using integral_comp_neg (f := f) (a := (0:ℝ)) (b := a)
    rw [← hcn]
    exact integral_congr (fun x _ => heven x)
  rw [hmirror] at hadd
  linarith

lemma cos_pi_mul_interval_eq (M : ℕ) :
    ∫ x in (-(1/2):ℝ)..(1/2), Real.cos (Real.pi * x) ^ (2*M)
      = 2 * Real.pi⁻¹ * ∫ x in (0:ℝ)..(Real.pi/2), Real.cos x ^ (2*M) := by
  have hsub : ∫ x in (-(1/2):ℝ)..(1/2), Real.cos (Real.pi * x) ^ (2*M)
      = Real.pi⁻¹ * ∫ x in (-(Real.pi/2))..(Real.pi/2), Real.cos x ^ (2*M) := by
    rw [integral_comp_mul_left (f := fun u : ℝ => Real.cos u ^ (2*M)) Real.pi_ne_zero]
    simp only [smul_eq_mul]
    rw [show Real.pi * (-(1/2)) = -(Real.pi/2) by ring,
        show Real.pi * (1/2) = Real.pi/2 by ring]
  have heven := integral_neg_self_eq_two_mul (fun u : ℝ => Real.cos u ^ (2*M))
      (Real.pi/2) (by intro x; simp [Real.cos_neg]) (Real.continuous_cos.pow (2*M))
  rw [hsub, heven]
  ring

end Work.ChiSmallWallis
