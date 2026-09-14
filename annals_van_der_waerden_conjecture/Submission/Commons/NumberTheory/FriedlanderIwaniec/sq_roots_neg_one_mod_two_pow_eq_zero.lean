import Mathlib.NumberTheory.SumTwoSquares

/-!
# Square roots of `-1` modulo powers of two

For `e ≥ 2` the congruence `α ^ 2 ≡ -1 (mod 2 ^ e)` has no solution: reducing any
solution modulo `4` (which is legitimate because `4 ∣ 2 ^ e`) would produce a square
root of `-1` in `ZMod 4`, and `ZMod 4` has no such element.

We prove the slightly more general statement that `α ^ 2 = -1` has no solution in
`ZMod n` whenever `4 ∣ n`, and deduce the power-of-two case.
-/

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- In `ZMod 4` no element squares to `-1` (the squares in `ZMod 4` are `0` and `1`,
while `-1 = 3`). -/
theorem sq_ne_neg_one_zmod_four (z : ZMod 4) : z ^ 2 ≠ -1 := by
  change Fin 4 at z
  fin_cases z <;> decide

/-- `-1` is not a square in `ZMod 4`. -/
theorem not_isSquare_neg_one_zmod_four : ¬ IsSquare (-1 : ZMod 4) := by
  rintro ⟨x, hx⟩
  exact sq_ne_neg_one_zmod_four x (by rw [pow_two]; exact hx.symm)

/-- If `4 ∣ n`, then the equation `α ^ 2 = -1` has no solution in `ZMod n`:
if `α` were one, its reduction modulo `4` (possible since `4 ∣ n`) would be a square
root of `-1` in `ZMod 4`, which does not exist. -/
theorem sq_roots_neg_one_eq_zero_of_four_dvd {n : ℕ} (hn : 4 ∣ n) :
    ({α : ZMod n | α ^ 2 = -1}.ncard) = 0 := by
  have hnot : ¬ IsSquare (-1 : ZMod n) := fun hs =>
    not_isSquare_neg_one_zmod_four (ZMod.isSquare_neg_one_of_dvd hn hs)
  have hempty : {α : ZMod n | α ^ 2 = -1} = (∅ : Set (ZMod n)) := by
    ext α
    constructor
    · intro hα
      change α ^ 2 = -1 at hα
      refine absurd ⟨α, ?_⟩ hnot
      rw [pow_two] at hα
      exact hα.symm
    · intro h
      exact h.elim
  rw [hempty]
  exact Set.ncard_empty _

/-- For `e ≥ 2` the equation `α ^ 2 = -1` has no solution in `ZMod (2 ^ e)`, because
`4 = 2 ^ 2` divides `2 ^ e`. -/
lemma sq_roots_neg_one_mod_two_pow_eq_zero {e : ℕ} (he : 2 ≤ e) :
    ({α : ZMod (2 ^ e) | α ^ 2 = -1}.ncard) = 0 := by
  apply sq_roots_neg_one_eq_zero_of_four_dvd
  have h : 2 ^ 2 ∣ 2 ^ e := Nat.pow_dvd_pow 2 he
  simpa using h

end Commons.NumberTheory.FriedlanderIwaniec