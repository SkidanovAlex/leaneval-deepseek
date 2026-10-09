import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The nontrivial square root of unity, as a unit

`Work.SSGRoute.HRec.negUnit L` is `-1` as a unit of a field `L`, together with the two facts that
make it the nontrivial element of `μ₂(L)`:

* `negUnit_mul_self : negUnit L * negUnit L = 1`,
* `negUnit_ne_one : negUnit L ≠ 1`.

This is the value taken by a `μ₂`-valued `2`-cocycle (such as the level Kummer cocycle
`DualMod 2 T → μ₂ ↪ Lˣ`) at a nontrivial pair; cf. `Work.SSGRoute.HRec.cupClassSetup.signUnit`
for the same object in the `HRec` coefficient-map setting.  It is stated here independently of the
(coupon-heavy) `HRecP2Imports` bundle so that the archimedean local criterion can be stated and
proved without it.
-/

namespace Work.SSGRoute.HRec

noncomputable section

/-- `-1` as a unit of a field. -/
def negUnit (L : Type) [Field L] : Lˣ := Units.mk (-1) (-1) (by ring) (by ring)

@[simp] lemma negUnit_val (L : Type) [Field L] : ((negUnit L : Lˣ) : L) = -1 := rfl

lemma negUnit_mul_self (L : Type) [Field L] : negUnit L * negUnit L = 1 := by
  ext; simp [negUnit]

lemma negUnit_ne_one (L : Type) [Field L] [CharZero L] : negUnit L ≠ 1 := by
  intro h
  have h1 : ((-1 : L)) = 1 := congrArg (fun u : Lˣ => (u : L)) h
  have h2 : (2 : L) = 0 := by linear_combination -h1
  exact Nat.cast_ne_zero.mpr (by norm_num : (2 : ℕ) ≠ 0) h2

end

end Work.SSGRoute.HRec
