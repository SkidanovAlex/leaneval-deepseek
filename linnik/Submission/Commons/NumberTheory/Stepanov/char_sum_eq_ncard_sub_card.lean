import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace Commons.NumberTheory.Stepanov

theorem char_sum_eq_ncard_sub_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (g : Polynomial F) :
    (∑ a : F, (quadraticChar F (g.eval a) : ℤ))
      = (({p : F × F | p.2 ^ 2 = g.eval p.1} : Set (F × F)).ncard : ℤ) - Fintype.card F := by
  let e : ({p : F × F | p.2 ^ 2 = g.eval p.1} : Set (F × F))
      ≃ (Σ a : F, {y : F // y ^ 2 = g.eval a}) :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => by rcases q with ⟨a, y, hy⟩; rfl }
  have hterm : ∀ a : F, (Fintype.card {y : F // y ^ 2 = g.eval a} : ℤ)
      = quadraticChar F (g.eval a) + 1 := by
    intro a
    have h1 : Fintype.card {y : F // y ^ 2 = g.eval a}
        = (Set.toFinset {y : F | y ^ 2 = g.eval a}).card :=
      (Set.toFinset_card {y : F | y ^ 2 = g.eval a}).symm
    rw [h1]
    exact quadraticChar_card_sqrts hF (g.eval a)
  have hcard : ((({p : F × F | p.2 ^ 2 = g.eval p.1} : Set (F × F)).ncard : ℤ))
      = ∑ a : F, (quadraticChar F (g.eval a) + 1) := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    rw [Fintype.card_congr e, Fintype.card_sigma]
    push_cast
    exact Finset.sum_congr rfl (fun a _ => hterm a)
  have hsplit : (∑ a : F, (quadraticChar F (g.eval a) + 1))
      = (∑ a : F, quadraticChar F (g.eval a)) + Fintype.card F := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    simp
  have hfin : ((({p : F × F | p.2 ^ 2 = g.eval p.1} : Set (F × F)).ncard : ℤ))
      = (∑ a : F, quadraticChar F (g.eval a)) + Fintype.card F := by
    rw [hcard, hsplit]
  linarith

end Commons.NumberTheory.Stepanov