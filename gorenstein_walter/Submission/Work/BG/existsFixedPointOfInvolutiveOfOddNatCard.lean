import Mathlib

namespace Work.BG

set_option linter.style.haveILetI false

/-- An involution on a finite set of odd cardinality has a fixed point.

The set of non-fixed points of an involution `f` is a disjoint union of the `2`-element
orbits `{x, f x}`, hence has even cardinality.  Since `Nat.card α` is odd, the set of fixed
points is odd and in particular nonempty.  Formally the contrapositive is the statement that
the number of fixed points of `f` is congruent to `Nat.card α` modulo `2`, which is a special
case of `Equiv.Perm.card_fixedPoints_modEq`; here we use the packaged result
`Equiv.Perm.exists_fixed_point_of_prime` for the prime `2`. -/
theorem existsFixedPointOfInvolutiveOfOddNatCard {α : Type} [Finite α] (f : α → α)
    (hf : Function.Involutive f) (hodd : Odd (Nat.card α)) : ∃ x, f x = x := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have hcard : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  rw [hcard] at hodd
  -- `hodd` says `2 ∤ Fintype.card α`
  have h2 : ¬ 2 ∣ Fintype.card α := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  -- view `f` as a permutation of order dividing `2`
  let σ : Equiv.Perm α := hf.toPerm f
  have hσ : σ ^ (2 ^ 1) = 1 := by
    show σ ^ 2 = 1
    ext x
    simp [σ, pow_two, Function.Involutive.coe_toPerm, hf x]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) h2 hσ
  exact ⟨a, by simpa [σ, Function.Involutive.coe_toPerm] using ha⟩

end Work.BG
