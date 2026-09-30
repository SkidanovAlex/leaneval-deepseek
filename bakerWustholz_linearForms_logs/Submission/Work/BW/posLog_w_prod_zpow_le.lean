import Mathlib
import Submission.Work.BW.est15defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The integer `|s| * m` is nonnegative, so its `.toNat` cast back to `ℝ` is the real product
`|s| · m`. -/
lemma toNat_abs_mul_cast (s : ℤ) (m : ℕ) :
    ((((|s| * (m : ℤ)).toNat : ℕ)) : ℝ) = ((|s| : ℤ) : ℝ) * (m : ℝ) := by
  have hnn : (0 : ℤ) ≤ |s| * (m : ℤ) := by positivity
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  push_cast
  ring

/-- Raising `y` to the integer power `s * m` is the same as raising `estBeta s y` (that is, `y` if
`s ≥ 0` and `y⁻¹` otherwise) to the nonnegative power `|s| * m`. -/
lemma zpow_mul_eq_estBeta_zpow {K : Type*} [Field K] (y : K) (s : ℤ) (m : ℕ) :
    y ^ (s * (m : ℤ)) = estBeta s y ^ ((((|s| * (m : ℤ)).toNat : ℕ)) : ℤ) := by
  have hnn : (0 : ℤ) ≤ |s| * (m : ℤ) := by positivity
  rw [Int.toNat_of_nonneg hnn]
  by_cases hs : 0 ≤ s
  · rw [estBeta, ite_eq_left hs, abs_of_nonneg hs]
  · rw [estBeta, ite_eq_right hs, abs_of_neg (not_le.mp hs), inv_zpow']
    congr 1
    ring

/-- The `estBeta` base commutes with a finite place: `w (estBeta s a) = estBeta s (w a)`. -/
lemma map_estBeta {K : Type*} [Field K] [NumberField K] (w : NumberField.FinitePlace K)
    (s : ℤ) (a : K) : w (estBeta s a) = estBeta s (w a) := by
  by_cases hs : 0 ≤ s <;> simp [estBeta, hs, map_inv₀]

theorem posLog_w_prod_zpow_le {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (w : NumberField.FinitePlace K) (a : Fin r → K) (s : ℤ) (J : ℕ)
    (m D : Fin r → ℕ) (hmD : ∀ j, (m j : ℝ) ≤ (D j : ℝ) / 2 ^ J) :
    Real.posLog (w (∏ j, a j ^ (s * (m j : ℤ))))
      ≤ (((|s| : ℤ) : ℝ) / 2 ^ J) * ∑ j, (D j : ℝ) * Real.posLog (w (estBeta s (a j))) := by
  have hprod : w (∏ j, a j ^ (s * (m j : ℤ)))
      = ∏ j, (w (estBeta s (a j))) ^ (((|s| * (m j : ℤ)).toNat : ℕ)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [map_zpow₀ w (a j) (s * (m j : ℤ)), map_estBeta w s (a j), ← zpow_natCast]
    exact zpow_mul_eq_estBeta_zpow (w (a j)) s (m j)
  rw [hprod]
  calc Real.posLog (∏ j, (w (estBeta s (a j))) ^ (((|s| * (m j : ℤ)).toNat : ℕ)))
      ≤ ∑ j, Real.posLog ((w (estBeta s (a j))) ^ (((|s| * (m j : ℤ)).toNat : ℕ))) :=
        Real.posLog_prod Finset.univ _
    _ = ∑ j, (((|s| * (m j : ℤ)).toNat : ℕ) : ℝ) * Real.posLog (w (estBeta s (a j))) := by
        simp only [Real.posLog_pow]
    _ ≤ ∑ j, (((|s| : ℤ) : ℝ) / 2 ^ J) * (D j : ℝ)
            * Real.posLog (w (estBeta s (a j))) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hc : 0 ≤ Real.posLog (w (estBeta s (a j))) := Real.posLog_nonneg
        have hns : (0 : ℝ) ≤ ((|s| : ℤ) : ℝ) := by positivity
        have hle : ((((|s| * (m j : ℤ)).toNat : ℕ)) : ℝ) ≤ (((|s| : ℤ) : ℝ) / 2 ^ J) * (D j : ℝ) := by
          rw [toNat_abs_mul_cast]
          calc ((|s| : ℤ) : ℝ) * (m j : ℝ)
              ≤ ((|s| : ℤ) : ℝ) * ((D j : ℝ) / 2 ^ J) :=
                mul_le_mul_of_nonneg_left (hmD j) hns
            _ = (((|s| : ℤ) : ℝ) / 2 ^ J) * (D j : ℝ) := by ring
        exact mul_le_mul_of_nonneg_right hle hc
    _ = (((|s| : ℤ) : ℝ) / 2 ^ J) * ∑ j, (D j : ℝ) * Real.posLog (w (estBeta s (a j))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

end Work.BW
