import Mathlib

set_option linter.style.haveILetI false

namespace Work.CORE4

open MulAction

/-- **A `p`-group normalising a subgroup fixes `p`-many elements of the centralizer.**

Let `G` be a finite group, `p` a prime, and let `X ≤ N_G(K)` be a subgroup with `|X| = p`.
If `p ∣ |K|` then `p ∣ |K ⊓ C_G(X)|`.

Proof.  Since `|X| = p` is a prime power, `X` is a `p`-group, and because `X ≤ N_G(K)` the
conjugation action of `G` on itself restricts to a multiplicative action of `X` on `K`.
For a `p`-group acting on a finite set the number of fixed points is congruent to the
cardinality of the set modulo `p`
(`IsPGroup.card_modEq_card_fixedPoints`), so
`|fixedPoints X K| ≡ |K| ≡ 0 (mod p)`.
Finally the fixed points of this action are exactly the elements of `K` commuting with every
element of `X`, i.e. the subgroup `K ⊓ C_G(X)`, so `Nat.card (fixedPoints X ↥K)` equals
`Nat.card ↥(K ⊓ Subgroup.centralizer (X : Set G))`. -/
theorem PGroupActionCentralizer {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {K X : Subgroup G} (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hXcard : Nat.card X = p) (hdvd : p ∣ Nat.card ↥K) : p ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (X : Set G)) := by
  -- `p` is prime, so we may use the `Fact` instances of Mathlib's `p`-group API.
  haveI hpFact : Fact p.Prime := ⟨hp⟩
  -- `X` is a group of order `p`, hence a `p`-group.
  have hXP : IsPGroup p X := IsPGroup.of_card (by rw [hXcard, pow_one])
  -- The conjugation action of `X` on `K`, obtained by restricting the conjugation action of
  -- `N_G(K)` on `K` along the inclusion `X ≤ N_G(K)`.
  let g : X →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom (H := K)).comp (Subgroup.inclusion hXK)
  letI : MulAction X ↥K := MulAction.compHom ↥K g
  -- The action is literally conjugation.
  have hval : ∀ (x : X) (k : ↥K), ((x • k : ↥K) : G) = (x : G) * (k : G) * (x : G)⁻¹ :=
    fun _ _ => rfl
  -- The fixed points of the action are the elements of `K` commuting with all of `X`.
  have hcard : Nat.card (fixedPoints X ↥K) =
      Nat.card ↥(K ⊓ Subgroup.centralizer (X : Set G)) := by
    apply Nat.card_congr
    refine
      { toFun := fun q => ⟨(q.1 : G), ⟨q.1.2, ?_⟩⟩
        invFun := fun q => ⟨⟨(q.1 : G), q.2.1⟩, ?_⟩
        left_inv := fun q => Subtype.ext rfl
        right_inv := fun q => Subtype.ext rfl }
    · -- a fixed point commutes with every element of `X`
      change (q.1 : G) ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun z : ↥K => (z : G)) (q.2 ⟨x, hx⟩)
      simp only [hval] at h
      have := congrArg (· * (x : G)) h
      simpa [mul_assoc] using this
    · -- an element of `K` commuting with `X` is a fixed point
      rw [MulAction.mem_fixedPoints]
      intro x
      apply Subtype.ext
      rw [hval]
      have hx : (x : G) * (q.1 : G) = (q.1 : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp q.2.2) (x : G) x.2
      rw [hx, mul_assoc, mul_inv_cancel, mul_one]
  -- For a `p`-group action the number of fixed points is congruent to the set's cardinality.
  have hmod : Nat.card ↥K ≡ Nat.card (fixedPoints X ↥K) [MOD p] :=
    hXP.card_modEq_card_fixedPoints ↥K
  have hdvd' : p ∣ Nat.card (fixedPoints X ↥K) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hdvd.modEq_zero_nat)
  rwa [hcard] at hdvd'

end Work.CORE4
