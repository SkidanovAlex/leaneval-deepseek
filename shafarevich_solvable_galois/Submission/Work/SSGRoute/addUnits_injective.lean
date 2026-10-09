import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-! ## Divisibility of the units of an algebraically closed field

`Ωˣ` for an algebraically closed field `Ω` is a divisible (rootable) group: every unit has an
`n`-th root, because `X ^ n - u` has a root in `Ω` which is automatically nonzero.  A divisible
abelian group is injective as a `ℤ`-module (Baer's criterion), and this is exactly the extension
property used by `addUnits_injective` below. -/

/-- The units of an algebraically closed field are rootable: every unit admits an `n`-th root. -/
noncomputable instance instRootableByUnitsNat (Ω : Type*) [Field Ω] [IsAlgClosed Ω] :
    RootableBy Ωˣ ℕ :=
  rootableByOfPowLeftSurj Ωˣ ℕ fun {n} hn => by
    intro u
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : Ω) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := fun h => by
      rw [h, zero_pow hn] at hz
      exact Units.ne_zero u hz.symm
    exact ⟨Units.mk0 z hz0, by ext; simpa using hz⟩

/-- `Additive Ωˣ` is divisible by `ℕ`. -/
noncomputable instance instDivisibleByAddUnitsNat (Ω : Type*) [Field Ω] [IsAlgClosed Ω] :
    DivisibleBy (Additive Ωˣ) ℕ where
  div a n := if hn : n = 0 then 0 else Additive.ofMul (RootableBy.root (Additive.toMul a) n)
  div_zero a := by simp
  div_cancel a hn := by
    rw [dif_neg hn, ← ofMul_pow, RootableBy.root_cancel (Additive.toMul a) hn]
    rfl

/-- `Additive Ωˣ` is divisible by `ℤ`. -/
noncomputable instance instDivisibleByAddUnitsInt (Ω : Type*) [Field Ω] [IsAlgClosed Ω] :
    DivisibleBy (Additive Ωˣ) ℤ :=
  AddGroup.divisibleByIntOfDivisibleByNat _

/-- **Extension of additive characters with values in `Ωˣ`.** An injective additive map
`f : M →+ N` allows any homomorphism `M →+ Additive Ωˣ` to be pushed forward to `N`, because
`Additive Ωˣ` is a divisible group, hence injective in abelian groups. -/
theorem addUnits_injective {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {M N : Type} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (hf : Function.Injective f)
    (g : M →+ Additive Ωˣ) : ∃ h : N →+ Additive Ωˣ, ∀ x, h (f x) = g x := by
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Ωˣ)).extension_property_addMonoidHom f hf g
  exact ⟨h, fun x => by simpa using DFunLike.congr_fun hh x⟩

end Work.SSGRoute
