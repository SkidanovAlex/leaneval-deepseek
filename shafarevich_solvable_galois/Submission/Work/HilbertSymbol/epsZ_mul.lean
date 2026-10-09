import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-! ## Multiplicativity of `epsZ`

`epsZ u` records the residue class of the unit `u : ℤ_[2]ˣ` modulo `4`, via
`u ≡ 1 + 2 ε(u) (mod 4)`.  Concretely `epsZ u = (ū.val / 2 : ZMod 2)` where `ū` is the image of
`u` in `(ZMod 4)ˣ`.  Since `(ZMod 4)ˣ = {1, -1}` is cyclic of order two, this map is a group
homomorphism `(ZMod 4)ˣ → ZMod 2` (with `ZMod 2` written additively); multiplicativity of `epsZ`
then follows from multiplicativity of `PadicInt.toZModPow`. -/

/-- The group homomorphism `(ZMod 4)ˣ → ZMod 2` sending `1 ↦ 0` and `-1 ↦ 1`, i.e. reading off
`(x - 1) / 2` from the representative of `x`. -/
def chi (x : (ZMod 4)ˣ) : ZMod 2 := ((x : ZMod 4).val / 2 : ℕ)

theorem chi_mul (x y : (ZMod 4)ˣ) : chi (x * y) = chi x + chi y := by
  fin_cases x <;> fin_cases y <;> decide

/-- `epsZ` is the composite of `chi` with reduction modulo `4`. -/
theorem epsZ_eq_chi (u : ℤ_[2]ˣ) :
    epsZ u = chi (Units.map (PadicInt.toZModPow (p := 2) 2) u) := rfl

theorem epsZ_mul (u v : ℤ_[2]ˣ) : epsZ (u * v) = epsZ u + epsZ v := by
  rw [epsZ_eq_chi (u * v), map_mul, chi_mul, ← epsZ_eq_chi u, ← epsZ_eq_chi v]

end Work.HilbertSymbol
