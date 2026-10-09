import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Divisibility implies injectivity for the `PTExt` coefficient module

`SSGRoute.PTExt.Coeff` is `NK.HassePrinciple.CoeffInt.{0} = ULift.{0} ℤ`, so a
`Coeff`-module structure on an additive commutive group `A` is the same thing as the
canonical `ℤ`-module structure on `A`: `ULift.{0} ℤ` is canonically isomorphic to `ℤ`
(`ULift.ringEquiv`) and the `ULift`-module structure is the one induced by `ULift.down`
(`ULift.smul_def` is `rfl`, `ULift.module`).

Over a principal ideal domain, an injective module is exactly a divisible one.  For `ℤ`
this is `Module.Baer.of_divisible` (Baer's criterion applied to the principal ideals
`(n) ⊆ ℤ`) together with `Module.Baer.injective`, both in
`Mathlib/Algebra/Category/Grp/Injective.lean`.  The statement below transports the
resulting `ℤ`-injectivity along the ring isomorphism `ℤ ≃+* ULift.{0} ℤ` using
`Module.Injective.of_ringEquiv`, the semilinear equivalence being the identity of `A`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- An additive commutative group that is divisible (in the sense that `n • x = y` is
solvable for every positive `n`) is an injective module over the coefficient ring
`SSGRoute.PTExt.Coeff = ULift.{0} ℤ`. -/
theorem moduleInjective_coeff_of_divisible (A : Type) [AddCommGroup A]
    (hdiv : ∀ (n : ℕ), 0 < n → ∀ y : A, ∃ x : A, n • x = y) :
    Module.Injective SSGRoute.PTExt.Coeff A := by
  -- Divisibility by every positive natural, as a `DivisibleBy A ℕ` instance.
  have hnat : DivisibleBy A ℕ :=
    divisibleByOfSMulRightSurj A ℕ (fun {n} hn => fun y => hdiv n (Nat.pos_of_ne_zero hn) y)
  -- Divisibility by `ℕ` upgrades to divisibility by `ℤ`.
  have hint : DivisibleBy A ℤ := AddGroup.divisibleByIntOfDivisibleByNat A
  haveI := hnat
  haveI := hint
  -- Baer's criterion over `ℤ`: divisible `ℤ`-modules are injective.
  have hinjZ : Module.Injective ℤ A := (Module.Baer.of_divisible A).injective
  -- Transfer along `ℤ ≃+* ULift.{0} ℤ`, i.e. `ULift.down`, whose inverse is `ULift.up`.
  let e₁ : ℤ ≃+* SSGRoute.PTExt.Coeff := (ULift.ringEquiv (R := ℤ)).symm
  haveI : RingHomInvPair (↑e₁ : ℤ →+* SSGRoute.PTExt.Coeff)
      (↑e₁.symm : SSGRoute.PTExt.Coeff →+* ℤ) := RingHomInvPair.of_ringEquiv e₁
  haveI : RingHomInvPair (↑e₁.symm : SSGRoute.PTExt.Coeff →+* ℤ)
      (↑e₁ : ℤ →+* SSGRoute.PTExt.Coeff) := RingHomInvPair.of_ringEquiv_symm e₁
  -- The identity of `A` is semilinear for `ULift.up : ℤ →+* Coeff`
  -- (`ULift.smul_def` holds by `rfl`).
  let e₂ : A ≃ₛₗ[(↑e₁ : ℤ →+* SSGRoute.PTExt.Coeff)] A :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => rfl }
  exact Module.Injective.of_ringEquiv e₁ e₂

end Work.SSGRoute
