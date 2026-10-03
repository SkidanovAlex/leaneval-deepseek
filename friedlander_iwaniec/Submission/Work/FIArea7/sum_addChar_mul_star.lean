import Mathlib
import Submission.Work.FIArea7.omega_orthogonality

namespace Work.FIArea7

open scoped BigOperators

/-- **Character orthogonality with complex conjugation.**

For a finite abelian group `G`, summing `χ z * conj (χ w)` over all additive characters
`χ : Additive G →+ ℂ` gives the order of `G` when `z = w` and `0` otherwise.  This is the
usual orthogonality of the character table, expressed with `star` in place of conjugation;
it is deduced from the additive orthogonality `sum_char_ite'` together with
`star_char'` (which identifies `conj (χ w)` with `χ w⁻¹`). -/
theorem sum_addChar_mul_star {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (z w : G) :
    (∑ χ : AddChar (Additive G) ℂ, χ (Additive.ofMul z) * star (χ (Additive.ofMul w)))
      = if z = w then (Fintype.card G : ℂ) else 0 := by
  have h : ∀ χ : AddChar (Additive G) ℂ,
      χ (Additive.ofMul z) * star (χ (Additive.ofMul w)) = χ (Additive.ofMul (z * w⁻¹)) := by
    intro χ
    rw [star_char' χ w, ← AddChar.map_add_eq_mul, ofMul_mul]
  simp_rw [h]
  rw [sum_char_ite']
  simp only [mul_inv_eq_one]

end Work.FIArea7
