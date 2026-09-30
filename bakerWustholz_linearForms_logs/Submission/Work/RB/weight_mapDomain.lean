import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weight of a `mapDomain`ed finsupp

If `f : α → β` and `s : α →₀ ℕ`, then pushing `s` forward along `f` and taking the weight
with respect to `w : β → M` agrees with taking the weight of `s` with respect to the
pullback weight `w ∘ f`.  This is the formal statement that the monomial exponents of a
`rename`/substitution pull back weights exactly.
-/

namespace Work.RB

theorem weight_mapDomain {α β M : Type*} [AddCommMonoid M] (w : β → M) (f : α → β)
    (s : α →₀ ℕ) : Finsupp.weight w (s.mapDomain f) = Finsupp.weight (w ∘ f) s := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  exact Finsupp.sum_mapDomain_index (fun b => by simp) (fun b m₁ m₂ => by simp [add_smul])

end Work.RB
