import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

open Work.ZeroDensity.Jutila.BzCross

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
lemma czSqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  rw [hsq]
  have := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  linarith

lemma czEps_compare {c Y : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hY : 1 ≤ Y) {R : ℕ} (hR1 : 1 ≤ R)
    (hRY : Y ≤ (R : ℝ) + 1) :
    Work.ZeroDensity.Jutila.BzCross.czEps c R ≤ 2 * Work.ZeroDensity.Jutila.BzCross.czEps (c / 2) Y := by
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  have hYpos : (0 : ℝ) < Y := by linarith
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg hR1'
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- `Y ≤ 2R`, hence `log Y ≤ log 2 + log R`
  have hY2R : Y ≤ 2 * (R : ℝ) := by linarith
  have hlogle : Real.log Y ≤ Real.log 2 + Real.log (R : ℝ) := by
    have h1 : Real.log Y ≤ Real.log (2 * (R : ℝ)) := Real.log_le_log hYpos hY2R
    have h2 : Real.log (2 * (R : ℝ)) = Real.log 2 + Real.log (R : ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hRpos)
    linarith
  -- `√(log Y) ≤ √(log 2) + √(log R)`
  have hsY : Real.sqrt (Real.log Y) ≤ Real.sqrt (Real.log 2) + Real.sqrt (Real.log (R : ℝ)) := by
    have h1 : Real.sqrt (Real.log Y) ≤ Real.sqrt (Real.log 2 + Real.log (R : ℝ)) :=
      Real.sqrt_le_sqrt hlogle
    have h2 := czSqrt_add_le hlog2nonneg hlogR
    linarith
  -- numeric bound: `√(log 2) ≤ 2 log 2`
  have hsqrtlog2 : Real.sqrt (Real.log 2) ≤ 2 * Real.log 2 := by
    have h1 : Real.sqrt (Real.log 2) ≤ 1 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith [Real.log_two_lt_d9]
    have h2 : 1 ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hc2 : 0 ≤ c / 2 := by linarith
  have hSY : (c / 2) * Real.sqrt (Real.log Y) ≤ c * Real.sqrt (Real.log (R : ℝ)) + Real.log 2 := by
    have step1 : (c / 2) * Real.sqrt (Real.log Y)
        ≤ (c / 2) * Real.sqrt (Real.log 2) + (c / 2) * Real.sqrt (Real.log (R : ℝ)) := by
      calc (c / 2) * Real.sqrt (Real.log Y)
          ≤ (c / 2) * (Real.sqrt (Real.log 2) + Real.sqrt (Real.log (R : ℝ))) :=
            mul_le_mul_of_nonneg_left hsY hc2
        _ = (c / 2) * Real.sqrt (Real.log 2) + (c / 2) * Real.sqrt (Real.log (R : ℝ)) := by ring
    have step2 : (c / 2) * Real.sqrt (Real.log 2) ≤ Real.log 2 := by
      have h1 : (c / 2) * Real.sqrt (Real.log 2) ≤ (1 / 2) * Real.sqrt (Real.log 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      have h2 : (1 / 2) * Real.sqrt (Real.log 2) ≤ Real.log 2 := by linarith
      linarith
    have step3 : (c / 2) * Real.sqrt (Real.log (R : ℝ)) ≤ c * Real.sqrt (Real.log (R : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    linarith
  have hkey : -(c * Real.sqrt (Real.log (R : ℝ)))
      ≤ Real.log 2 + -((c / 2) * Real.sqrt (Real.log Y)) := by linarith
  calc Work.ZeroDensity.Jutila.BzCross.czEps c R
      = Real.exp (-(c * Real.sqrt (Real.log (R : ℝ)))) := rfl
    _ ≤ Real.exp (Real.log 2 + -((c / 2) * Real.sqrt (Real.log Y))) :=
        Real.exp_le_exp.mpr hkey
    _ = Real.exp (Real.log 2) * Real.exp (-((c / 2) * Real.sqrt (Real.log Y))) :=
        Real.exp_add (Real.log 2) (-((c / 2) * Real.sqrt (Real.log Y)))
    _ = 2 * Real.exp (-((c / 2) * Real.sqrt (Real.log Y))) := by
        rw [Real.exp_log (by norm_num)]
    _ = 2 * Work.ZeroDensity.Jutila.BzCross.czEps (c / 2) Y := rfl

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
