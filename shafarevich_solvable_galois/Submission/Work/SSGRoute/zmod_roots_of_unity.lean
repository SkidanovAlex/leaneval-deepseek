import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The multiplicative iso `ZMod n ≃* μ_n(R)` of a primitive root of unity

Given a primitive `n`-th root of unity `ζ` in a domain `R`, the powers of `ζ` identify the
additive group `ZMod n` with the group `μ_n(R) = rootsOfUnity n R` of `n`-th roots of unity.
This file packages that identification as the `MulEquiv` `zr`, together with the basic
evaluation lemma (the value at the class of an integer `i` is `ζ ^ i`).
-/
open scoped Classical

namespace Work.SSGRoute

/-- The multiplicative isomorphism `Multiplicative (ZMod n) ≃* μ_n(R)` sending the class of
`i` to `ζ ^ i`, for `ζ` a primitive `n`-th root of unity. -/
noncomputable def zr {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    [NeZero n] {ζ : Rˣ} (hζ : IsPrimitiveRoot ζ n) :
    Multiplicative (ZMod n) ≃* ↥(rootsOfUnity n R) :=
  hζ.zmodEquivZPowers.toMultiplicativeLeft.trans (MulEquiv.subgroupCongr hζ.zpowers_eq)

/-- Evaluation of `zr` at the class of an integer. -/
lemma zr_apply_int {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ n) (i : ℤ) :
    ((zr hζ (Multiplicative.ofAdd ((i : ZMod n))) : ↥(rootsOfUnity n R)) : Rˣ) = ζ ^ i := by
  rw [show (zr hζ (Multiplicative.ofAdd ((i : ZMod n))) : ↥(rootsOfUnity n R))
      = (MulEquiv.subgroupCongr hζ.zpowers_eq)
          (Additive.toMul (hζ.zmodEquivZPowers (i : ZMod n))) from rfl]
  rw [MulEquiv.subgroupCongr_apply]
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_int]
  rfl

end Work.SSGRoute
