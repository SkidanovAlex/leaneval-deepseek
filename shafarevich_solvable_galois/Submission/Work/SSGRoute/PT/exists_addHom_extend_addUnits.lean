import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Extending additive characters valued in `Ωˣ` along an injective homomorphism

If `Ω` is an algebraically closed field, every unit of `Ω` has an `n`-th root, hence the
multiplicative group `Ωˣ`, viewed additively, is a divisible abelian group.  A divisible abelian
group is injective in the category of abelian groups (Baer's criterion,
`Module.Baer.of_divisible`), and injectivity is precisely the extension property proved here:

for every injective additive homomorphism `ι : M →+ N` of abelian groups and every additive
character `φ : M →+ Additive Ωˣ`, there is an additive character `ψ : N →+ Additive Ωˣ`
restricting to `φ` along `ι`.
-/

namespace Work.SSGRoute.PT

/-- Every unit of an algebraically closed field has an `n`-th root (for `n ≠ 0`):
surjectivity of the `n`-th power map on `Ωˣ`. -/
theorem units_root_exists_aux {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (n : ℕ) (hn : n ≠ 0) (u : Ωˣ) : ∃ v : Ωˣ, v ^ n = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : Ω) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := fun h => by
    rw [h, zero_pow hn] at hz
    exact Units.ne_zero u hz.symm
  exact ⟨Units.mk0 z hz0, by ext; simpa using hz⟩

/-- Any additive homomorphism from a subgroup `ι : M →+ N` into `Additive Ωˣ` extends to `N`,
`Ω` being algebraically closed: `Additive Ωˣ` is divisible, hence injective as an abelian group.
-/
theorem exists_addHom_extend_addUnits {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (ι : M →+ N) (hι : Function.Injective ι) (φ : M →+ Additive Ωˣ) :
    ∃ ψ : N →+ Additive Ωˣ, ψ.comp ι = φ := by
  have hdiv : DivisibleBy (Additive Ωˣ) ℤ := by
    haveI : DivisibleBy (Additive Ωˣ) ℕ :=
      divisibleByOfSMulRightSurj (Additive Ωˣ) ℕ (fun {n} hn x => by
        obtain ⟨v, hv⟩ := units_root_exists_aux n hn (Additive.toMul x)
        exact ⟨Additive.ofMul v, by
          rw [← Additive.toMul.injective.eq_iff]
          simpa only [toMul_nsmul, toMul_ofMul] using hv⟩)
    exact AddGroup.divisibleByIntOfDivisibleByNat (Additive Ωˣ)
  exact (@Module.Baer.of_divisible (Additive Ωˣ) _ hdiv).extension_property_addMonoidHom ι hι φ

end Work.SSGRoute.PT
