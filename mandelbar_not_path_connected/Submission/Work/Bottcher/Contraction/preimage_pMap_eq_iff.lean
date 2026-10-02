/-
# The explicit preimages of `p_c(z) = (z^2 + conj c)^2 + c`

The holomorphic quartic `pMap c = T_c ∘ T_c` has, over any point `w`, exactly the
four preimages `± sqrt (± sqrt (w - c) - conj c)` (principal square root): solve
`u^2 = w - c` and then `z^2 = u - conj c`.  These explicit formulas are the
backbone of the *inverse-branch* construction of the analytic Böttcher coordinate:
every inverse branch of `p_c` is one of these four square-root expressions, so no
inverse function theorem is needed to *write down* the candidates.
-/
import Submission.Work.Bottcher.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

/-- `(sqrt v)^2 = v` for the principal complex square root. -/
theorem sqrt_sq (v : ℂ) : Complex.sqrt v ^ 2 = v := by
  rw [Complex.sqrt]
  exact Complex.cpow_nat_inv_pow v (by norm_num)

/-- The two preimages of a quadratic equation: `(z^2 + A)^2 = B` iff
`z^2 = ± sqrt B - A`. -/
theorem sq_add_sq_eq_iff (A B z : ℂ) :
    (z ^ 2 + A) ^ 2 = B ↔ z ^ 2 = Complex.sqrt B - A ∨ z ^ 2 = -Complex.sqrt B - A := by
  constructor
  · intro h
    rcases eq_or_eq_neg_of_sq_eq_sq (z ^ 2 + A) (Complex.sqrt B) (by rw [h, sqrt_sq]) with h' | h'
    · exact Or.inl (by linear_combination h')
    · exact Or.inr (by linear_combination h')
  · rintro (h | h)
    · have hh : z ^ 2 + A = Complex.sqrt B := by linear_combination h
      rw [hh, sqrt_sq]
    · have hh : z ^ 2 + A = -Complex.sqrt B := by linear_combination h
      rw [hh, neg_sq, sqrt_sq]

/-- **The four explicit preimages of `p_c`.** -/
theorem preimage_pMap_eq_iff (c w z : ℂ) :
    Work.Bottcher.pMap c z = w ↔
      (z = Complex.sqrt (Complex.sqrt (w - c) - conj c) ∨
       z = -Complex.sqrt (Complex.sqrt (w - c) - conj c) ∨
       z = Complex.sqrt (-Complex.sqrt (w - c) - conj c) ∨
       z = -Complex.sqrt (-Complex.sqrt (w - c) - conj c)) := by
  have h0 : Work.Bottcher.pMap c z = w ↔ (z ^ 2 + conj c) ^ 2 = w - c := by
    rw [Work.Bottcher.pMap_apply]
    constructor <;> intro h <;> linear_combination h
  rw [h0, sq_add_sq_eq_iff]
  constructor
  · rintro (h | h)
    · rcases eq_or_eq_neg_of_sq_eq_sq z (Complex.sqrt (Complex.sqrt (w - c) - conj c))
        (by rw [h, sqrt_sq]) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases eq_or_eq_neg_of_sq_eq_sq z (Complex.sqrt (-Complex.sqrt (w - c) - conj c))
        (by rw [h, sqrt_sq]) with h' | h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
  · rintro (rfl | rfl | rfl | rfl)
    · left; rw [sqrt_sq]
    · left; rw [neg_sq, sqrt_sq]
    · right; rw [sqrt_sq]
    · right; rw [neg_sq, sqrt_sq]

end Work.Bottcher.Contraction
