import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Series.Deleg.rpowMajorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.WtDerivAux

open scoped Real

/-- The mode weight `(2m+1)/(λ_m √(2m+1))` decays like `√2/4 · m^{-3/2}`, hence is summable.

Indeed for `m ≥ 1` the numerator and the `Real.sqrt` cancel:
`(2m+1)/(λ_m √(2m+1)) = √(2m+1)/λ_m ≤ √2·√(m+1)/(m+1)^2 = √2·(m+1)^{-3/2}`,
using `λ_m = 2m(2m+5) ≥ (m+1)^2` and `2m+1 ≤ 2(m+1)`, and `Σ_m (m+1)^{-3/2}` converges.
At `m = 0` the quotient is `0` because `λ_0 = 0` and division by zero is total in `ℝ`. -/
theorem summable_lam_sqrt :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 1)
      / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
  -- the comparison series `∑ (m+1)^{-3/2}`
  have hbase : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(3 / 2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(3 / 2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  refine Summable.of_norm_bounded (hbase.mul_left (Real.sqrt 2)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  by_cases hm : m = 0
  · -- the zeroth term vanishes since `λ_0 = 0`
    subst hm
    have h0 : (2 * ((0 : ℕ) : ℝ) + 1)
        / (Work.FTS.PhiStar.Gegenbauer.lam 0 * Real.sqrt (2 * ((0 : ℕ) : ℝ) + 1)) = 0 := by
      rw [show Work.FTS.PhiStar.Gegenbauer.lam 0 = 0 by norm_num [Work.FTS.PhiStar.Gegenbauer.lam]]
      norm_num
    rw [h0, abs_zero]
    positivity
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hlam_pos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hA : (0 : ℝ) ≤ (2 * (m : ℝ) + 1)
        / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
      div_nonneg (by positivity) (mul_nonneg hlam_pos.le (Real.sqrt_nonneg _))
    rw [abs_of_nonneg hA]
    have hsne : Real.sqrt (2 * (m : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hsq : Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)
        = 2 * (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
    -- cancel the `√(2m+1)` between numerator and denominator
    have hstep : (2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        = Real.sqrt (2 * (m : ℝ) + 1) / Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [div_eq_iff (mul_ne_zero (ne_of_gt hlam_pos) hsne)]
      have h1 : Real.sqrt (2 * (m : ℝ) + 1) / Work.FTS.PhiStar.Gegenbauer.lam m
          * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          = Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
        rw [div_mul_eq_mul_div,
          show Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            = Work.FTS.PhiStar.Gegenbauer.lam m
                * (Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) by ring,
          mul_div_cancel_left₀ _ (ne_of_gt hlam_pos)]
      rw [h1, hsq]
    rw [hstep]
    -- `√(2m+1) ≤ √2·√(m+1)`
    have hsle : Real.sqrt (2 * (m : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith)
    -- `(m+1)^2 ≤ λ_m`
    have hlam2 : ((m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hb2pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
    -- the `rpow` identity `√(m+1)/(m+1)^2 = (m+1)^{-3/2}`
    have hcore : Real.sqrt ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2
        = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_natCast ((m : ℝ) + 1) 2,
        ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
      congr 1
      norm_num
    calc Real.sqrt (2 * (m : ℝ) + 1) / Work.FTS.PhiStar.Gegenbauer.lam m
        ≤ (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1)) / Work.FTS.PhiStar.Gegenbauer.lam m :=
          div_le_div_of_nonneg_right hsle hlam_pos.le
      _ = Real.sqrt 2 * (Real.sqrt ((m : ℝ) + 1)
            / Work.FTS.PhiStar.Gegenbauer.lam m) := by ring
      _ ≤ Real.sqrt 2 * (Real.sqrt ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_left (Real.sqrt_nonneg ((m : ℝ) + 1)) hb2pos hlam2
      _ = Real.sqrt 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by rw [hcore]

end Work.FTS.PhiStar.FlatWAux.WtDerivAux
