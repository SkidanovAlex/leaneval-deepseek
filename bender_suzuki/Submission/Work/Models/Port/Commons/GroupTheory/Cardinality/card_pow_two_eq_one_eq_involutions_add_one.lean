import Mathlib.GroupTheory.OrderOfElement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Cardinality

/-- Elements of order `2` have square `1`. -/
lemma orderOf_eq_two_imp_sq_eq_one {G : Type*} [Group G] {x : G} (h : orderOf x = 2) :
    x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [h])

/-- An element with `x ^ 2 = 1` and `x ≠ 1` has order `2`. -/
lemma sq_eq_one_imp_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx : x ^ 2 = 1)
    (hne : x ≠ 1) : orderOf x = 2 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h2

/-- The solutions of `x ^ 2 = 1` in a group are the identity together with the
elements of order two. -/
noncomputable def powTwoEqOneEquivOption (G : Type*) [Group G] :
    {x : G // x ^ 2 = 1} ≃ Option {x : G // orderOf x = 2} := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun y => if h : (y : G) = 1 then none
      else some ⟨(y : G), sq_eq_one_imp_orderOf_eq_two y.2 h⟩
  · exact fun o => match o with
      | none => ⟨1, by simp⟩
      | some y => ⟨(y : G), orderOf_eq_two_imp_sq_eq_one y.2⟩
  · intro y
    by_cases h : (y : G) = 1
    · simp only [dif_pos h]
      exact Subtype.ext h.symm
    · simp only [dif_neg h]
  · intro o
    match o with
    | none => simp
    | some y =>
        have hy : (y : G) ≠ 1 := by
          intro h
          have h1 : orderOf (y : G) = 1 := by rw [h]; exact orderOf_one
          rw [y.2] at h1
          omega
        simp only [dif_neg hy]

theorem card_pow_two_eq_one_eq_involutions_add_one {G : Type*} [Group G] [Finite G] :
    Nat.card {x : G // x ^ 2 = 1} = Nat.card {x : G // orderOf x = 2} + 1 := by
  classical
  rw [Nat.card_congr (powTwoEqOneEquivOption G)]
  let _ : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]

end Commons.GroupTheory.Cardinality