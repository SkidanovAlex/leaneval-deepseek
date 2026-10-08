import Mathlib

namespace Work.BSW.S3

/-- Conjugate elements have the same order. -/
private lemma orderOf_eq_of_isConj {G : Type} [Group G] {p q : G} (hpq : IsConj p q) :
    orderOf p = orderOf q := by
  obtain ⟨c, hc⟩ := hpq
  exact SemiconjBy.orderOf_eq (c : G) hc

/-- If `Y` is a conjugacy-closed set of `G` of size `2a`, all of whose conjugacy classes
have `a` elements and none of whose elements is conjugate to its inverse, then all elements
of `Y` have the same order: `Y` is exactly the union of a single conjugacy class together
with that of its inverses. -/
theorem order_eq_of_two_classes {G : Type} [Group G] [Finite G] {Y : Set G} {a : ℕ}
    (hconj : ∀ g z : G, z ∈ Y → g * z * g⁻¹ ∈ Y)
    (hinv : ∀ z : G, z ∈ Y → z⁻¹ ∈ Y)
    (hclass : ∀ z : G, z ∈ Y → (conjugatesOf z).ncard = a)
    (hY : Y.ncard = 2 * a)
    (hnotconj : ∀ z : G, z ∈ Y → ¬ IsConj z z⁻¹) :
    ∀ y z : G, y ∈ Y → z ∈ Y → orderOf y = orderOf z := by
  intro y z hy hz
  -- The conjugacy class of `y` is contained in `Y`, by conjugation-closure.
  have hsub : conjugatesOf y ⊆ Y := by
    intro w hw
    obtain ⟨c, hc⟩ := isConj_iff.1 hw
    rw [← hc]
    exact hconj c y hy
  -- The conjugacy class of `y⁻¹` is contained in `Y`, using closure under inversion.
  have hsub' : conjugatesOf y⁻¹ ⊆ Y := by
    intro w hw
    obtain ⟨c, hc⟩ := isConj_iff.1 hw
    rw [← hc]
    exact hconj c y⁻¹ (hinv y hy)
  -- Since `y` is not conjugate to `y⁻¹`, the two classes are disjoint.
  have hdisj : Disjoint (conjugatesOf y) (conjugatesOf y⁻¹) := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    exact hnotconj y hy (hw1.trans hw2.symm)
  -- The union therefore has `a + a = 2a` elements, as does `Y`.
  have hcu : (conjugatesOf y ∪ conjugatesOf y⁻¹).ncard = 2 * a := by
    rw [Set.ncard_union_eq hdisj, hclass y hy, hclass y⁻¹ (hinv y hy)]
    omega
  have hYeq : conjugatesOf y ∪ conjugatesOf y⁻¹ = Y := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro w hw
      rcases hw with hw | hw
      · exact hsub hw
      · exact hsub' hw
    · rw [hY, hcu]
  -- Hence `z` is conjugate to `y` or to `y⁻¹`, and both have the order of `y`.
  have hz' : z ∈ conjugatesOf y ∪ conjugatesOf y⁻¹ := by rw [hYeq]; exact hz
  rcases hz' with h | h
  · exact orderOf_eq_of_isConj h
  · have := orderOf_eq_of_isConj h
    rwa [orderOf_inv] at this

end Work.BSW.S3
