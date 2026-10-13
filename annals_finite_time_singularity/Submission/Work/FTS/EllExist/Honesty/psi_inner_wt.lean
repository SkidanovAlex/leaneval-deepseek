import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set

/-- `w z = (1+z)^2/z^2`, so `z^p * w(z)^2 = z^(p-4) * (1+z)^4` on `z > 0`; integrating the
crude bound `(1+z)^4 ≤ (1+t)^4` against the exact power integral
`∫_0^t z^(p-4) = t^(p-3)/(p-3)` gives the stated weighted inner product bound. -/
theorem psi_inner_wt {p : ℝ} (hp : 4 ≤ p) {t : ℝ} (ht : 0 < t) :
    MeasureTheory.IntegrableOn (fun z => z ^ p * (Work.Spaces.w z) ^ 2) (Set.Ioo 0 t) ∧
    (∫ z in Set.Ioo 0 t, z ^ p * (Work.Spaces.w z) ^ 2)
      ≤ t ^ (p + 1) * (Work.Spaces.w t) ^ 2 / (p - 3) := by
  have hp4 : 0 ≤ p - 4 := by linarith
  have hw_sq : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 = (1 + z) ^ (4 : ℝ) / z ^ (4 : ℝ) := by
    intro z
    have hw_nat : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
      rw [Work.Spaces.w]; ring_nf
    rw [hw_nat]; norm_num
  have hpt : ∀ z ∈ Ioo (0 : ℝ) t,
      z ^ p * (Work.Spaces.w z) ^ 2 = z ^ (p - 4) * (1 + z) ^ (4 : ℝ) := by
    intro z hz
    rw [hw_sq z]
    have e : z ^ p * ((1 + z) ^ (4 : ℝ) / z ^ (4 : ℝ))
        = (z ^ p / z ^ (4 : ℝ)) * (1 + z) ^ (4 : ℝ) := by ring
    rw [e, ← Real.rpow_sub hz.1 p 4]
  have hcont : Continuous (fun z : ℝ => z ^ (p - 4) * (1 + z) ^ (4 : ℝ)) :=
    (Real.continuous_rpow_const hp4).mul
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4)).comp
        (continuous_const.add continuous_id))
  have hIntF : IntegrableOn (fun z : ℝ => z ^ (p - 4) * (1 + z) ^ (4 : ℝ)) (Ioo 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hcont.intervalIntegrable 0 t)
  have hcont2 : Continuous (fun z : ℝ => z ^ (p - 4) * (1 + t) ^ (4 : ℝ)) :=
    (Real.continuous_rpow_const hp4).mul continuous_const
  have hInt2 : IntegrableOn (fun z : ℝ => z ^ (p - 4) * (1 + t) ^ (4 : ℝ)) (Ioo 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hcont2.intervalIntegrable 0 t)
  have hIntG : IntegrableOn (fun z : ℝ => z ^ p * (Work.Spaces.w z) ^ 2) (Ioo 0 t) :=
    hIntF.congr_fun (fun z hz => (hpt z hz).symm) measurableSet_Ioo
  refine ⟨hIntG, ?_⟩
  have hmono : ∀ z ∈ Ioo (0 : ℝ) t,
      z ^ (p - 4) * (1 + z) ^ (4 : ℝ) ≤ z ^ (p - 4) * (1 + t) ^ (4 : ℝ) := by
    intro z hz
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (le_of_lt hz.1) _)
    exact Real.rpow_le_rpow (by linarith [hz.1] : (0 : ℝ) ≤ 1 + z)
      (by linarith [hz.2] : 1 + z ≤ 1 + t) (by norm_num)
  have hrpow : ∫ z in Ioo (0 : ℝ) t, z ^ (p - 4) = t ^ (p - 3) / (p - 3) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le]
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < p - 4))]
    rw [Real.zero_rpow (by linarith : p - 4 + 1 ≠ 0), sub_zero]
    rw [show p - 4 + 1 = p - 3 by ring]
  have hkey : t ^ (p + 1) * ((1 + t) ^ (4 : ℝ) / t ^ (4 : ℝ))
      = (1 + t) ^ (4 : ℝ) * t ^ (p - 3) := by
    have e : t ^ (p + 1) * ((1 + t) ^ (4 : ℝ) / t ^ (4 : ℝ))
        = (t ^ (p + 1) / t ^ (4 : ℝ)) * (1 + t) ^ (4 : ℝ) := by ring
    rw [e, ← Real.rpow_sub ht (p + 1) 4]
    rw [show (p + 1 : ℝ) - 4 = p - 3 by ring]
    ring
  calc ∫ z in Ioo (0 : ℝ) t, z ^ p * (Work.Spaces.w z) ^ 2
      = ∫ z in Ioo (0 : ℝ) t, z ^ (p - 4) * (1 + z) ^ (4 : ℝ) :=
          setIntegral_congr_fun measurableSet_Ioo (fun z hz => hpt z hz)
    _ ≤ ∫ z in Ioo (0 : ℝ) t, z ^ (p - 4) * (1 + t) ^ (4 : ℝ) :=
          setIntegral_mono_on hIntF hInt2 measurableSet_Ioo hmono
    _ = (1 + t) ^ (4 : ℝ) * ∫ z in Ioo (0 : ℝ) t, z ^ (p - 4) := by
          rw [integral_mul_const]; ring
    _ = (1 + t) ^ (4 : ℝ) * (t ^ (p - 3) / (p - 3)) := by rw [hrpow]
    _ = t ^ (p + 1) * (Work.Spaces.w t) ^ 2 / (p - 3) := by
          rw [hw_sq t, hkey]; ring

end Work.FTS.EllExist.Honesty
