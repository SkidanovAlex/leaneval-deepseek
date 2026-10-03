import Mathlib
import Submission.Work.Analysis.Interpolation.Basic

namespace Work.Analysis.Interpolation

open scoped ENNReal NNReal

/-- For a finite extended nonnegative real `U` and an exponent `p ≥ 0`, the extended power
`U ^ p` is `ENNReal.ofReal` of the ordinary real power of the "real part" `U.toReal`. -/
private lemma ofReal_toReal_rpow_of_ne_top {U : ℝ≥0∞} (hU : U ≠ ⊤) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (U.toReal ^ p) = U ^ p := by
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp, ENNReal.ofReal_toReal hU]

/-- If one of `U`, `V` is infinite then the other is zero, and both sides of the identity
below vanish (the powers are computed with positive exponents). -/
private lemma ofReal_toReal_const_eq_inf {m : ℝ} {U V : ℝ≥0∞} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hU : U = ⊤) (hV0 : V = 0) :
    ENNReal.ofReal (m * U.toReal ^ α * V.toReal ^ β) = ENNReal.ofReal m * U ^ α * V ^ β := by
  rw [hU, hV0, ENNReal.toReal_top, ENNReal.top_rpow_of_pos hα, ENNReal.zero_rpow_of_pos hβ]
  simp [Real.zero_rpow (ne_of_gt hα), Real.zero_rpow (ne_of_gt hβ)]

lemma ofReal_toReal_const_eq (m : ℝ) (hm : 0 ≤ m) (U V : ℝ≥0∞) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hU : U < ⊤ ∨ V = 0) (hV : V < ⊤ ∨ U = 0) : ENNReal.ofReal (m * U.toReal ^ α * V.toReal ^ β) = ENNReal.ofReal m * U ^ α * V ^ β := by
  by_cases hU1 : U = ⊤
  · -- `U = ⊤`, hence `V = 0` and both sides vanish.
    have hV0 : V = 0 := by
      rcases hU with h | h
      · rw [hU1] at h; exact absurd h (lt_irrefl ⊤)
      · exact h
    exact ofReal_toReal_const_eq_inf hα hβ hU1 hV0
  · by_cases hV1 : V = ⊤
    · -- `V = ⊤`, hence `U = 0` and both sides vanish.
      have hU0 : U = 0 := by
        rcases hV with h | h
        · rw [hV1] at h; exact absurd h (lt_irrefl ⊤)
        · exact h
      rw [hU0, hV1, ENNReal.toReal_top, ENNReal.top_rpow_of_pos hβ, ENNReal.zero_rpow_of_pos hα]
      simp [Real.zero_rpow (ne_of_gt hα), Real.zero_rpow (ne_of_gt hβ)]
    · -- both `U` and `V` are finite: distribute `ofReal` over the nonnegative product.
      have hUα : ENNReal.ofReal (U.toReal ^ α) = U ^ α :=
        ofReal_toReal_rpow_of_ne_top hU1 hα.le
      have hVβ : ENNReal.ofReal (V.toReal ^ β) = V ^ β :=
        ofReal_toReal_rpow_of_ne_top hV1 hβ.le
      rw [show m * U.toReal ^ α * V.toReal ^ β = m * (U.toReal ^ α * V.toReal ^ β) from
            mul_assoc _ _ _,
        ENNReal.ofReal_mul hm,
        ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg α),
        hUα, hVβ, mul_assoc]

end Work.Analysis.Interpolation
