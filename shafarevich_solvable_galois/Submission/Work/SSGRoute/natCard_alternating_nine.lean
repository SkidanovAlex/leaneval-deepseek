import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- For an additive homomorphism `f : A →+ B`, the source cardinality is the product of the
cardinalities of the range and the kernel: `|A| = |range f| * |ker f|`.
This is the first isomorphism theorem together with `|A| = |A ⧸ ker f| * |ker f|`. -/
lemma natCard_eq_card_range_mul_card_ker
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker]
  congr 1
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv

theorem natCard_alternating_nine
    {X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : Type*}
    [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃] [AddCommGroup X₄] [AddCommGroup X₅]
    [AddCommGroup X₆] [AddCommGroup X₇] [AddCommGroup X₈] [AddCommGroup X₉]
    [Finite X₁] [Finite X₂] [Finite X₃] [Finite X₄] [Finite X₅] [Finite X₆] [Finite X₇] [Finite X₈]
    [Finite X₉]
    (f₁₂ : X₁ →+ X₂) (f₂₃ : X₂ →+ X₃) (f₃₄ : X₃ →+ X₄) (f₄₅ : X₄ →+ X₅)
    (f₅₆ : X₅ →+ X₆) (f₆₇ : X₆ →+ X₇) (f₇₈ : X₇ →+ X₈) (f₈₉ : X₈ →+ X₉)
    (hinj : Function.Injective f₁₂)
    (h₂ : f₁₂.range = f₂₃.ker) (h₃ : f₂₃.range = f₃₄.ker) (h₄ : f₃₄.range = f₄₅.ker)
    (h₅ : f₄₅.range = f₅₆.ker) (h₆ : f₅₆.range = f₆₇.ker) (h₇ : f₆₇.range = f₇₈.ker)
    (h₈ : f₇₈.range = f₈₉.ker) (hsurj : Function.Surjective f₈₉) :
    Nat.card X₁ * Nat.card X₃ * Nat.card X₅ * Nat.card X₇ * Nat.card X₉ =
      Nat.card X₂ * Nat.card X₄ * Nat.card X₆ * Nat.card X₈ := by
  -- Express every `Nat.card Xᵢ` as a product of two consecutive range-cardinalities.
  have hX1 : Nat.card X₁ = Nat.card f₁₂.range :=
    Nat.card_congr (Equiv.ofInjective f₁₂ hinj)
  have hX2 : Nat.card X₂ = Nat.card f₂₃.range * Nat.card f₁₂.range := by
    rw [natCard_eq_card_range_mul_card_ker f₂₃, ← h₂]
  have hX3 : Nat.card X₃ = Nat.card f₃₄.range * Nat.card f₂₃.range := by
    rw [natCard_eq_card_range_mul_card_ker f₃₄, ← h₃]
  have hX4 : Nat.card X₄ = Nat.card f₄₅.range * Nat.card f₃₄.range := by
    rw [natCard_eq_card_range_mul_card_ker f₄₅, ← h₄]
  have hX5 : Nat.card X₅ = Nat.card f₅₆.range * Nat.card f₄₅.range := by
    rw [natCard_eq_card_range_mul_card_ker f₅₆, ← h₅]
  have hX6 : Nat.card X₆ = Nat.card f₆₇.range * Nat.card f₅₆.range := by
    rw [natCard_eq_card_range_mul_card_ker f₆₇, ← h₆]
  have hX7 : Nat.card X₇ = Nat.card f₇₈.range * Nat.card f₆₇.range := by
    rw [natCard_eq_card_range_mul_card_ker f₇₈, ← h₇]
  have hX8 : Nat.card X₈ = Nat.card f₈₉.range * Nat.card f₇₈.range := by
    rw [natCard_eq_card_range_mul_card_ker f₈₉, ← h₈]
  have hX9 : Nat.card X₉ = Nat.card f₈₉.range := by
    rw [AddMonoidHom.range_eq_top.mpr hsurj]
    exact (Nat.card_congr AddSubgroup.topEquiv.toEquiv).symm
  rw [hX1, hX2, hX3, hX4, hX5, hX6, hX7, hX8, hX9]
  ring

end Work.SSGRoute
