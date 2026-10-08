import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- A surjective homomorphism out of a finite group of odd order lands in a group of odd
order: the order of the image (which is the whole target) divides the order of the source,
and a divisor of an odd number is odd. -/
theorem odd_card_of_surjective {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hodd : Odd (Nat.card G)) : Odd (Nat.card H) := by
  -- `f` is surjective, so its range is the whole of `H`.
  have hrange : (f.range : Subgroup H) = ⊤ := MonoidHom.range_eq_top.mpr hf
  have hEqH : Nat.card (f.range : Subgroup H) = Nat.card H := by
    rw [hrange]
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  -- First isomorphism theorem: `G ⧸ ker f ≃* f.range`.
  have hquot : Nat.card (G ⧸ f.ker) = Nat.card (f.range : Subgroup H) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  -- Lagrange: `|G| = |G ⧸ ker f| * |ker f|`, so `|H|` divides `|G|`.
  have hdvd : Nat.card H ∣ Nat.card G := by
    rw [← hEqH, ← hquot]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    exact dvd_mul_right _ _
  exact hodd.of_dvd_nat hdvd

end Work.Skeleton
