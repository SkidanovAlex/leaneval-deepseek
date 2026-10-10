import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PTembedding

/-- The number of nontrivial group homomorphisms from a group `Q` of prime order `p`
into the cyclic group `Multiplicative (ZMod p)` (the additive group `ZMod p` written
multiplicatively) is `p - 1`.

Indeed, `Q` is cyclic; fixing a generator `g` of `Q`, a homomorphism is uniquely
determined by the image of `g`, and since both `Q` and `Multiplicative (ZMod p)` have
order `p`, every element is a valid image of `g`.  This gives a bijection between the
homomorphisms and the elements of the target, under which the trivial homomorphism
corresponds to the identity; hence there are `p - 1` nontrivial ones. -/
theorem natCard_nontrivHoms_primeCard (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
    (hQ : Nat.card Q = p) :
    Nat.card {φ : Q →* Multiplicative (ZMod p) // φ ≠ 1} = p - 1 := by
  classical
  haveI : IsCyclic Q := isCyclic_of_prime_card hQ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  -- the chosen generator has order `p`
  have hgord : orderOf g = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hQ]
  -- the target has order `p`
  have hA : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
  -- every element of the target has order dividing `orderOf g`
  have hdvd : ∀ a : Multiplicative (ZMod p), orderOf a ∣ orderOf g := by
    intro a
    rw [hgord]
    have h := orderOf_dvd_natCard a
    rwa [hA] at h
  -- a homomorphism is determined by, and can be prescribed on, the generator `g`;
  -- the trivial homomorphism corresponds to the target identity.
  let e : {φ : Q →* Multiplicative (ZMod p) // φ ≠ 1} ≃
      {a : Multiplicative (ZMod p) // a ≠ 1} :=
    { toFun := fun φ =>
        ⟨φ.1 g, fun h => φ.2 ((MonoidHom.eq_iff_eq_on_generator hg φ.1 1).mpr (by simpa using h))⟩
      invFun := fun a =>
        ⟨monoidHomOfForallMemZpowers hg (hdvd a.1), fun h => a.2 (by
          have h1 := congrArg (fun f : Q →* Multiplicative (ZMod p) => f g) h
          rw [monoidHomOfForallMemZpowers_apply_gen hg (hdvd a.1)] at h1
          simpa using h1)⟩
      left_inv := fun φ => Subtype.ext ((MonoidHom.eq_iff_eq_on_generator hg _ _).mpr (by
        rw [monoidHomOfForallMemZpowers_apply_gen hg (hdvd (φ.1 g))]))
      right_inv := fun a => Subtype.ext (monoidHomOfForallMemZpowers_apply_gen hg (hdvd a.1)) }
  rw [Nat.card_congr e]
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun a : Multiplicative (ZMod p) => a = 1)]
  simp [ZMod.card]

end Work.SSGRoute.PTembedding
