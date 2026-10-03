import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.eps_rightPow

namespace Work.OROneRel

/-- The exponent sum of a generator `t` in its own positive power `of t ^ n` is `n`. -/
lemma epsc_of_pow_self {α : Type*} (t : α) (n : ℕ) :
    Work.OROneRel.eps t ((FreeGroup.of t : FreeGroup α) ^ n) = n := by
  rw [← zpow_natCast (FreeGroup.of t) n, epsc_zpow, epsc_of_eq, mul_one]

/-- The exponent sum of a generator `t` in a positive power `of y ^ n` of a different generator
`y` is zero. -/
lemma epsc_of_pow_ne {α : Type*} {t y : α} (h : t ≠ y) (n : ℕ) :
    Work.OROneRel.eps t ((FreeGroup.of y : FreeGroup α) ^ n) = 0 := by
  rw [← zpow_natCast (FreeGroup.of y) n, epsc_zpow, epsc_of_ne h, mul_zero]

theorem eps_letterPow_mul_letterPow {α : Type*} {a b : α} (hab : a ≠ b) (p q : ℕ) :
    Work.OROneRel.eps a ((FreeGroup.of a)^p * (FreeGroup.of b)^q) = p ∧
      Work.OROneRel.eps b ((FreeGroup.of a)^p * (FreeGroup.of b)^q) = q := by
  constructor
  · rw [epsc_mul, epsc_of_pow_self a p, epsc_of_pow_ne hab q, add_zero]
  · rw [epsc_mul, epsc_of_pow_ne (Ne.symm hab) p, epsc_of_pow_self b q, zero_add]

end Work.OROneRel
