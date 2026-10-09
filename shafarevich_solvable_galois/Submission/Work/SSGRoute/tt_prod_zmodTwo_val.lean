import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If `a ^ 2 = 1` then `a ^ n` only depends on `n` modulo `2`. -/
private lemma pow_mod_two {G : Type*} [Monoid G] {a : G} (ha : a ^ 2 = 1) (n : ℕ) :
    a ^ (n % 2) = a ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 2]
  rw [pow_add, pow_mul, ha, one_pow, mul_one]

/-- Pointwise form: for `a` of exponent dividing two and `x y : ZMod 2`, the
exponent `(x + y).val` can be split additively. -/
private lemma zmodTwo_pow_add_val {G : Type*} [CommGroup G] (a : G) (ha : a * a = 1)
    (x y : ZMod 2) :
    a ^ ((x + y).val) = a ^ (x.val) * a ^ (y.val) := by
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact ha
  rw [ZMod.val_add, pow_mod_two ha2, pow_add]

theorem tt_prod_zmodTwo_val (G : Type*) [CommGroup G] (P : Type*) [Fintype P] (b : P → G)
    (hb : ∀ p, b p * b p = 1) (ε ε' : P → ZMod 2) :
    (∏ p, (b p) ^ ((ε p + ε' p).val)) =
      (∏ p, (b p) ^ ((ε p).val)) * (∏ p, (b p) ^ ((ε' p).val)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  exact zmodTwo_pow_add_val (b p) (hb p) (ε p) (ε' p)

end Work.SSGRoute
