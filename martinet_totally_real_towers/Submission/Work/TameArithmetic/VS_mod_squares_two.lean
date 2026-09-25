import Submission.Work.TameArithmetic.VS_eq_pm_squares
import Submission.Work.TameArithmetic.neg_one_mem_VS
import Submission.Work.TameArithmetic.neg_one_not_square

/-!
# `Work.TameArithmetic.VS_mod_squares_two`

**`dim_{𝔽₂}(V_S/ℚ^{×2}) = 1`**, in the form used by the arithmetic of the tame route: every element
of Koch's group `V_S` is a square or minus a square of a rational, and the class of `-1` is a
*nonzero* element of `V_S/ℚ^{×2}`.  Hence `V_S` is generated modulo squares by `{±1}`, i.e.
`V_S/ℚ^{×2} ≅ ℤ/2`, and the Shafarevich--Koch deficiency bound `r - d ≤ dim_{𝔽₂} V_S/ℚ^{×2}`
reads `r - d ≤ 1`, giving `r ≤ 6` for `d = |S| = 5` and finally
`4r ≤ 24 ≤ 25 = d²` (`Work.TameArithmetic.four_mul_le_sq_of_rel_card_le_six`).
-/

set_option autoImplicit false

namespace Work.TameArithmetic

/-- **`V_S/ℚ^{×2} ≅ ℤ/2`**, split into the two facts that are used: (i) every element of `V_S` is
`±` a square of a rational, and (ii) `-1 ∈ V_S` is not a square, so the two classes `1` and `-1`
exhaust `V_S/ℚ^{×2}`. -/
theorem VS_mod_squares_two :
    (∀ x : ℚˣ, x ∈ VS → (∃ y : ℚˣ, x = y * y) ∨ (∃ y : ℚˣ, x = - (y * y))) ∧
    ((-1 : ℚˣ) ∈ VS ∧ ¬ ∃ y : ℚˣ, (-1 : ℚˣ) = y * y) :=
  ⟨fun x hx => by
    obtain ⟨y, hy | hy⟩ := VS_eq_pm_squares.mp hx
    · exact Or.inl ⟨y, hy⟩
    · exact Or.inr ⟨y, hy⟩,
   neg_one_mem_VS, neg_one_not_square⟩

end Work.TameArithmetic
