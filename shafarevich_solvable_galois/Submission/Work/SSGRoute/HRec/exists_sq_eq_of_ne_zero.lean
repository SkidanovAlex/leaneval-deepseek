import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A nonzero element of an algebraically closed field is a square

The one API fact consumed by the `⟸` branch of the reverse Artin–Schreier dictionary
(`Submission/Work/SSGRoute/HRec/NOTES_exists_conjInv_kummerChar.md`).  Its contract for the caller:
given `x` with `x * x = algebraMap k Ω (a : k)`, the identity `Ψ x * Ψ x = φ a > 0` forces `Ψ x`
real (`2 u v = 0` in `Ψ x = u + v i`), step 3's `Ψ (c x) = star (Ψ x)` then gives `c x = x` by
injectivity of `Ψ`, and `x * c x = x * x = a` lands `a ∈ normSet c`.

(`IsAlgClosed.exists_pow_nat_eq` is stated with the element first and the exponent bound
implicit-then-explicit: `exists_pow_nat_eq a (hn : 0 < n)`.)
-/

noncomputable section

namespace Work.SSGRoute.HRec

theorem exists_sq_eq_of_ne_zero {Ω : Type} [Field Ω] [IsAlgClosed Ω] {a : Ω} (ha : a ≠ 0) :
    ∃ x : Ω, x * x = a := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by norm_num)
  exact ⟨x, by simpa [pow_two] using hx⟩

end Work.SSGRoute.HRec
