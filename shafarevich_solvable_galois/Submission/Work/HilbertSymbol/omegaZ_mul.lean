import Mathlib.NumberTheory.Padics.RingHoms
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-!
# Multiplicativity of `omegaZ`

`omegaZ u` is defined for a unit `u : ℤ_[2]ˣ` by looking at the residue class of `u` modulo `8`:
it is `0` if that class is `1` or `7` (i.e. `u ≡ ±1 (mod 8)`), and `1` otherwise.  Hence `omegaZ`
factors through the finite group `(ZMod (2^3))ˣ` of units modulo `8`, and the multiplicativity of
`omegaZ` is a finite check on that group.
-/

/-- `omegaZ` depends only on the residue class of `u` modulo `8`: the induced function on the
finite group `(ZMod (2^3))ˣ = (ZMod 8)ˣ`. -/
def omegaZMod (x : (ZMod (2 ^ 3))ˣ) : ZMod 2 :=
  if (x : ZMod (2 ^ 3)).val = 1 ∨ (x : ZMod (2 ^ 3)).val = 7 then 0 else 1

/-- `omegaZ` is the composite of reduction modulo `8` with `omegaZMod`. -/
theorem omegaZ_eq_omegaZMod (u : ℤ_[2]ˣ) :
    omegaZ u = omegaZMod (Units.map (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) u) := rfl

/-- `omegaZMod` is a group homomorphism `(ZMod 8)ˣ → ZMod 2`; this is a finite verification. -/
theorem omegaZMod_mul (x y : (ZMod (2 ^ 3))ˣ) :
    omegaZMod (x * y) = omegaZMod x + omegaZMod y := by
  fin_cases x <;> fin_cases y <;> decide

theorem omegaZ_mul (u v : ℤ_[2]ˣ) : omegaZ (u * v) = omegaZ u + omegaZ v := by
  rw [omegaZ_eq_omegaZMod u, omegaZ_eq_omegaZMod v, omegaZ_eq_omegaZMod (u * v)]
  rw [map_mul, omegaZMod_mul]

end Work.HilbertSymbol
