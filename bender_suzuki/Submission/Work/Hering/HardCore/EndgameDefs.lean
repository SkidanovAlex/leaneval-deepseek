import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Matrices for the endgame of the abelian case of the hard core of Hering's theorem

`C_m = Ω_m(C) ≅ (ℤ/2^m)³` carries the conjugation action of the two group elements `s` and `t`
of the proof.  In the basis `(c₁, c₂, c₃)` the actions are the matrices `SMat` and `TMat` below,
written with the convention that the *columns* are the images of the basis vectors.
-/

open Matrix

namespace Work.Hering.HardCore

/-- The action of `s` on `C_m`: `c₁ ↦ -c₁`, `c₂ ↦ c₂`, `c₃ ↦ c₂ - c₃`. -/
def SMat (m : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ m)) :=
  !![(-1 : ZMod (2 ^ m)), 0, 0; 0, 1, 1; 0, 0, -1]

/-- The general form of the action of `t` on `C_m` in the parametrisation of the proof:
`c₁ ↦ -c₁`, `c₂ ↦ -c₂ + d`, `c₃ ↦ -c₃ + k · d`, where `d = c₁ + 2k₂c₂ + 2k₃c₃`. -/
def TMat (m : ℕ) (k k₂ k₃ : ZMod (2 ^ m)) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ m)) :=
  !![(-1 : ZMod (2 ^ m)), 1, k; 0, 2 * k₂ - 1, 2 * k * k₂; 0, 2 * k₃, 2 * k * k₃ - 1]

end Work.Hering.HardCore
