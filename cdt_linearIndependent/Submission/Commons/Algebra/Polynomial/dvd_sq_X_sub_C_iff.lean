import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div

namespace Commons.Algebra.Polynomial

/-- `(X − C β)^2` divides `p` iff `β` is a double root of `p`, i.e. `p` and `p'` both vanish at
`β`. -/
theorem dvd_sq_X_sub_C_iff {K : Type*} [Field K] (p : Polynomial K) (β : K) :
    (Polynomial.X - Polynomial.C β) ^ 2 ∣ p
      ↔ p.eval β = 0 ∧ p.derivative.eval β = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    constructor
    · simp
    · simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
  · rintro ⟨h0, h1⟩
    obtain ⟨q, rfl⟩ :=
      (Polynomial.dvd_iff_isRoot).mpr (by simpa [Polynomial.IsRoot.def] using h0)
    have hderiv : (Polynomial.derivative ((Polynomial.X - Polynomial.C β) * q)).eval β
        = q.eval β := by
      simp [Polynomial.derivative_mul]
    have hq : q.eval β = 0 := by
      rw [← hderiv]; exact h1
    obtain ⟨r, rfl⟩ :=
      (Polynomial.dvd_iff_isRoot).mpr (by simpa [Polynomial.IsRoot.def] using hq)
    exact ⟨r, by ring⟩

end Commons.Algebra.Polynomial