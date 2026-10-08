import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.OrderOfElement

theorem card_orderOf_eq_two_eq_card_sq_eq_one_sub_one {G : Type*} [Group G] [Finite G] :
    Nat.card {t : G // orderOf t = 2} = Nat.card {t : G // t ^ 2 = 1} - 1 := by
  classical
  -- An element has `t ^ 2 = 1` iff it is trivial or has order exactly `2`.
  have h2 : ∀ t : G, t ^ 2 = 1 ↔ t = 1 ∨ orderOf t = 2 := by
    intro t
    rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_prime (by norm_num), orderOf_eq_one_iff]
  -- No element of order `2` is trivial.
  have hne : ∀ t : {t : G // orderOf t = 2}, (t : G) ≠ 1 := by
    intro t h
    have : orderOf (t : G) = 1 := by rw [orderOf_eq_one_iff]; exact h
    rw [t.2] at this
    exact absurd this (by norm_num)
  -- Hence the solutions of `t ^ 2 = 1` are the involutions, plus the identity.
  let e : {t : G // t ^ 2 = 1} ≃ {t : G // orderOf t = 2} ⊕ Unit :=
  { toFun := fun x =>
      if hx : (x : G) = 1 then Sum.inr ()
      else Sum.inl ⟨x, ((h2 x).mp x.2).resolve_left hx⟩
    invFun := fun y => match y with
      | Sum.inl t => ⟨t, (h2 t).mpr (Or.inr t.2)⟩
      | Sum.inr _ => ⟨1, by simp⟩
    left_inv := by
      intro x
      by_cases hx : (x : G) = 1
      · simp only [hx, dif_pos]
        exact Subtype.ext hx.symm
      · simp only [hx, dif_neg, not_false_iff]
    right_inv := by
      intro y
      rcases y with t | u
      · have ht : (t : G) ≠ 1 := hne t
        simp only [ht, dif_neg, not_false_iff]
      · cases u
        simp }
  have hunit : Nat.card Unit = 1 := Nat.card_unique
  have hcard : Nat.card {t : G // t ^ 2 = 1} = Nat.card {t : G // orderOf t = 2} + 1 := by
    rw [Nat.card_congr e, Nat.card_sum, hunit]
  omega

end Commons.GroupTheory.OrderOfElement