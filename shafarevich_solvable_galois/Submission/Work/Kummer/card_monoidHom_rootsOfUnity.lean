import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Kummer

/-- The monoid of homomorphisms from a finite commutative group `G` of exponent dividing `n`
into the group of `n`-th roots of unity of `K` has the same cardinality as `G`, whenever `K`
has enough `n`-th roots of unity.

This is the character-duality count used in Kummer theory: over a field containing a primitive
`n`-th root of unity, the `n`-torsion character group of a finite abelian group of exponent
dividing `n` is isomorphic to the group itself. -/
theorem card_monoidHom_rootsOfUnity {G K : Type*} [CommGroup G] [Finite G] [CommMonoid K]
    {n : ℕ} [NeZero n] (hexp : ∀ g : G, g ^ n = 1) [HasEnoughRootsOfUnity K n] :
    Nat.card (G →* rootsOfUnity n K) = Nat.card G := by
  -- `K` has enough `n`-th roots of unity and `Monoid.exponent G ∣ n`, hence it also has enough
  -- `Monoid.exponent G`-th roots of unity.
  have : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)
  -- A homomorphism `G →* Kˣ` lands in `rootsOfUnity n K` since `G` has exponent dividing `n`;
  -- this gives a bijection with `G →* rootsOfUnity n K`.
  have key : (G →* rootsOfUnity n K) ≃ (G →* Kˣ) :=
  { toFun := fun f => (rootsOfUnity n K).subtype.comp f
    invFun := fun φ => φ.codRestrict (rootsOfUnity n K) (fun g => by
      rw [mem_rootsOfUnity, ← map_pow, hexp g, map_one])
    left_inv := fun f => by ext g; rfl
    right_inv := fun φ => by ext g; rfl }
  rw [Nat.card_congr key]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G K

end Work.Kummer
