import Mathlib
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.epsZ_primeUnit
import Submission.Work.HilbertSymbol.signOf_intCast
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-- `signOf` at a natural number cast into `ZMod 2` is `(-1) ^ m` in `ℤˣ`. -/
theorem signOf_natCast (m : ℕ) : signOf ((m : ℕ) : ZMod 2) = (-1 : ℤˣ) ^ m := by
  rw [show ((m : ℕ) : ZMod 2) = ((m : ℤ) : ZMod 2) by push_cast; ring]
  rw [signOf_intCast, zpow_natCast]

/-- `intUnitOf` of `(-1) ^ k` is the corresponding power of `(-1)` in `ℤˣ`. -/
theorem intUnitOf_neg_one_pow (k : ℕ) : intUnitOf ((-1 : ℤ) ^ k) = (-1 : ℤˣ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpm : (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := by
      rcases Nat.even_or_odd k with h | h
      · exact Or.inl h.neg_one_pow
      · exact Or.inr h.neg_one_pow
    rw [pow_succ, intUnitOf_mul hpm (Or.inr rfl), ih, pow_succ]
    simp

/-- For odd `n`, `n / 2 = (n - 1) / 2`. -/
theorem div_two_eq_of_odd {n : ℕ} (h : n % 2 = 1) : n / 2 = (n - 1) / 2 := by
  have hn : n = 2 * (n / 2) + 1 := by
    have := Nat.div_add_mod n 2
    omega
  have h1 : n - 1 = 2 * (n / 2) := by omega
  rw [h1, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]

/-- The `signOf`-value of `ε(p)` for an odd prime `p` is the Legendre symbol of `-1`. -/
theorem signOf_epsZ_primeUnit (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    signOf (epsZ (unitPart 2 (primeUnit p))) = intUnitOf (legendreSym p (-1)) := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  rw [epsZ_primeUnit p hp, legendreSym.at_neg_one hp, ZMod.χ₄_eq_neg_one_pow hodd,
    ← div_two_eq_of_odd hodd, signOf_natCast, intUnitOf_neg_one_pow]

end Work.HilbertSymbol
