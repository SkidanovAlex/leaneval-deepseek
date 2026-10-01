import Mathlib.Algebra.Field.Defs
import Mathlib.SetTheory.Cardinal.Finite

namespace Commons.FieldTheory.Finite

/-- For `m ≠ 0` and `d > 0`, the fiber of `x ↦ x ^ d` over `m` in a field `K` has
the same cardinality as the fiber of `u ↦ u ^ d` over the unit `Units.mk0 m hm0`
in the unit group `Kˣ`: every solution `y` of `y ^ d = m` is automatically
nonzero (hence a unit), and conversely every unit solution coerces to a field
solution. -/
theorem card_pow_fiber_eq_units_fiber {K : Type*} [Field K]
    (m : K) (hm0 : m ≠ 0) (d : ℕ) (hd : 0 < d) :
    Nat.card {y : K // y ^ d = m} = Nat.card {u : Kˣ // u ^ d = Units.mk0 m hm0} := by
  let toU : {y : K // y ^ d = m} → {u : Kˣ // u ^ d = Units.mk0 m hm0} := by
    intro y
    have hy : y.1 ≠ 0 := by
      intro hy0
      have hm : m = 0 := by
        calc
          m = y.1 ^ d := y.2.symm
          _ = 0 ^ d := by rw [hy0]
          _ = 0 := zero_pow (Nat.ne_of_gt hd)
      exact hm0 hm
    refine ⟨Units.mk0 y.1 hy, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    rw [Units.val_mk0]
    rw [Units.val_mk0]
    exact y.2
  let fromU : {u : Kˣ // u ^ d = Units.mk0 m hm0} → {y : K // y ^ d = m} := by
    intro u
    refine ⟨(u.1 : K), ?_⟩
    have hu := congrArg (fun w : Kˣ => (w : K)) u.2
    rw [Units.val_pow_eq_pow_val, Units.val_mk0] at hu
    exact hu
  have hleft : Function.LeftInverse fromU toU := by
    intro y
    apply Subtype.ext
    simp [toU, fromU, Units.val_mk0]
  have hright : Function.LeftInverse toU fromU := by
    intro u
    apply Subtype.ext
    apply Units.ext
    simp [toU, fromU]
  exact Nat.card_congr
    { toFun := toU
      invFun := fromU
      left_inv := hleft
      right_inv := hright }

end Commons.FieldTheory.Finite