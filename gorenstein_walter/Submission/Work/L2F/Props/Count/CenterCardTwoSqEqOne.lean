import Mathlib

namespace Work.L2F.Props.Count

/-- In a group of cardinality two, the square of every element is the identity:
the order of an element divides the order of the group, hence is `1` or `2`. -/
lemma sq_eq_one_of_card_eq_two {H : Type*} [Group H] (h : Nat.card H = 2) (x : H) :
    x ^ 2 = 1 := by
  have hdvd : orderOf x ∣ 2 := by rw [← h]; exact orderOf_dvd_natCard x
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · rw [orderOf_eq_one_iff] at h1
    rw [h1]
    simp
  · have := pow_orderOf_eq_one x
    rwa [h2] at this

/-- If a subgroup `N` has two elements, then every element of `N` has order dividing
two, i.e. is an involution. -/
theorem CenterCardTwoSqEqOne {G : Type*} [Group G] (N : Subgroup G) (hN : Nat.card N = 2) :
    ∀ w ∈ N, w ^ 2 = 1 := by
  intro w hw
  have hx : (⟨w, hw⟩ : N) ^ 2 = 1 := sq_eq_one_of_card_eq_two hN ⟨w, hw⟩
  have hx' : w ^ 2 = 1 := by
    have := congrArg (Subgroup.subtype N) hx
    simpa using this
  exact hx'

end Work.L2F.Props.Count
