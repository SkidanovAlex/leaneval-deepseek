import Mathlib
import Submission.Work.QuadraticFields.discr_eq_of_sq_eq_squarefree

namespace Work.QuadraticFields

/-- **The parity of the discriminant of `ℚ(√d)`.**

Let `K` be a number field generated over `ℚ` by an element `x` with `x ^ 2 = d`, where `d` is a
squarefree integer.  Then `2` divides `disc K` if and only if `d ≢ 1 (mod 4)`: for `d ≡ 1 (mod 4)`
the field has fundamental discriminant `d` (odd), while for `d ≡ 2, 3 (mod 4)` its discriminant is
`4 d` (even).

Since squarefreeness of `d` excludes `d ≡ 0 (mod 4)`, this is the classical parity criterion for
quadratic fields, and it is immediate from the exact computation
`disc K = d * (if d % 4 = 1 then 1 else 4)` of `discr_eq_of_sq_eq_squarefree`. -/
theorem two_dvd_discr_iff_mod_four_ne_one {K : Type*} [Field K] [NumberField K] {d : ℤ}
    (hd : Squarefree d) (x : K) (hx : x ^ 2 = algebraMap ℚ K (d : ℚ))
    (hgen : Algebra.adjoin ℚ ({x} : Set K) = ⊤) :
    ((2 : ℤ) ∣ NumberField.discr K) ↔ d % 4 ≠ 1 := by
  rw [discr_eq_of_sq_eq_squarefree hd x hx hgen]
  by_cases h1 : d % 4 = 1
  · -- `d ≡ 1 (mod 4)`: the discriminant is `d`, which is odd.
    rw [ite_eq_left h1, mul_one]
    have hnd : ¬ ((2 : ℤ) ∣ d) := by
      rintro ⟨k, hk⟩
      omega
    constructor
    · intro h; exact absurd h hnd
    · intro h; exact absurd h1 h
  · -- `d ≡ 2, 3 (mod 4)`: the discriminant is `4 * d`, which is even.
    rw [ite_eq_right h1]
    exact ⟨fun _ => h1, fun _ => ⟨2 * d, by ring⟩⟩

end Work.QuadraticFields
