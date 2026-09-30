import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `Work.Pi6.EMZ.freePart`

`(Fin r → ℤ)` is `p`-divisible exactly when `r = 0`.  Indeed, any element of `Fin r → ℤ` is
`p`-divisible iff `ℤ` is, and `ℤ` is `p`-divisible only for `p = 1` (here `p ≥ 2`): the constant
function `1` has no `p`-th root because `p · y = 1` in `ℤ` forces `p = ±1`.

This is the trivial-`ℤ`-part fact: the first homology of a space is a free abelian group, so the
`p`-divisibility of `H_1(-;ℤ)` detects whether that free part vanishes.
-/

namespace Work.Pi6.EMZ

/-- In `ℤ`, a product equal to `1` with a factor `p ≥ 2` is impossible. -/
private lemma natCast_mul_eq_one_imp_false {p : ℕ} (hp : 2 ≤ p) {y : ℤ}
    (h : (p : ℤ) * y = 1) : False := by
  obtain h1 | h1 := Int.eq_one_or_neg_one_of_mul_eq_one h <;> omega

theorem freePart {r p : ℕ} (hp : 2 ≤ p) :
    (∀ x : Fin r → ℤ, ∃ y : Fin r → ℤ, p • y = x) ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    have hi : 0 < r := Nat.pos_of_ne_zero hr
    obtain ⟨y, hy⟩ := h (fun _ => 1)
    have h1 : (p : ℤ) * y ⟨0, hi⟩ = 1 := by
      have := congrFun hy ⟨0, hi⟩
      simpa using this
    exact natCast_mul_eq_one_imp_false hp h1
  · rintro rfl x
    exact ⟨x, by ext i; exact i.elim0⟩

end Work.Pi6.EMZ
