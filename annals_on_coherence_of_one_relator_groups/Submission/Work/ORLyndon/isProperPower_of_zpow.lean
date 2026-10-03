import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# A generator power is a proper power as soon as `|s| ≥ 2`

For a generator `a` of the free group and an integer exponent `s : ℤ` with `2 ≤ s.natAbs`,
`FreeGroup.of a ^ s` is a proper power (`Work.OROneRel.IsProperPower`, i.e. a `k`-th power with
`k ≥ 2`).  The root is

* `FreeGroup.of a` when `s > 0`,
* `(FreeGroup.of a)⁻¹` when `s < 0`,

i.e. `FreeGroup.of a ^ s.sign`, and the exponent is `s.natAbs`.  The two cases are covered at once
by `Int.sign_mul_natAbs`, `s.sign * (s.natAbs : ℤ) = s`, together with `zpow_mul`.

This is the contrapositive direction used when passing from "`r` is not a proper power" to the
shape of a terminal relator `r = of x ^ m`, where necessarily `m.natAbs = 1`.
-/

namespace Work.ORLyndon

/-- `(of a) ^ s` is a proper power whenever `|s| ≥ 2`: namely the `s.natAbs`-th power of
`of a ^ s.sign` (which is `of a` for `s > 0` and `(of a)⁻¹` for `s < 0`), since
`s.sign * s.natAbs = s`. -/
theorem isProperPower_of_zpow {α : Type*} (a : α) {s : ℤ} (hs : 2 ≤ s.natAbs) :
    Work.OROneRel.IsProperPower (FreeGroup.of a ^ s) := by
  refine ⟨FreeGroup.of a ^ s.sign, s.natAbs, hs, ?_⟩
  exact (calc (FreeGroup.of a ^ s.sign) ^ (s.natAbs : ℤ)
      = FreeGroup.of a ^ (s.sign * (s.natAbs : ℤ)) :=
        (zpow_mul (FreeGroup.of a) s.sign (s.natAbs : ℤ)).symm
    _ = FreeGroup.of a ^ s := by rw [Int.sign_mul_natAbs]).symm

end Work.ORLyndon
