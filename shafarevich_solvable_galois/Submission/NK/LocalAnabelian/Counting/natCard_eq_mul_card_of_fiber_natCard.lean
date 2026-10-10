import Mathlib.SetTheory.Cardinal.Finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalAnabelian.Counting

/-- If every fibre of `f : α → β` has `n` elements (`n > 0`) and `β` is finite,
then `α` has `n * |β|` elements. -/
theorem natCard_eq_mul_card_of_fiber_natCard {α β : Type*} (f : α → β) (n : ℕ)
    (hn : 0 < n) [Finite β]
    (hfib : ∀ b : β, Nat.card {a : α // f a = b} = n) :
    Nat.card α = n * Nat.card β := by
  let hβ : Fintype β := Fintype.ofFinite β
  have hfiber : ∀ b : β, Finite {a : α // f a = b} := fun b =>
    Nat.finite_of_card_ne_zero (by rw [hfib b]; exact hn.ne')
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
  rw [Nat.card_sigma]
  simp_rw [hfib]
  rw [Nat.card_eq_fintype_card, Finset.sum_const, Finset.card_univ]
  exact Nat.mul_comm _ _

end NK.LocalAnabelian.Counting
