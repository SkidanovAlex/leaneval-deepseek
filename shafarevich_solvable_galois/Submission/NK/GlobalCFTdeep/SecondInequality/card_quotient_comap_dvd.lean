import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality

/-- For a group homomorphism `f : A →* B` and a normal subgroup `N ⊴ B`, the quotient
`A ⧸ f⁻¹(N)` embeds into `B ⧸ N` (the induced map has trivial kernel), so its cardinality divides
that of `B ⧸ N`.  Both quotients are assumed nonempty and finite (i.e. `Nat.card ≠ 0`). -/
theorem card_quotient_comap_dvd {A B : Type*} [Group A] [Group B] (f : A →* B) (N : Subgroup B)
    [N.Normal] (hA : Nat.card (A ⧸ N.comap f) ≠ 0) (hB : Nat.card (B ⧸ N) ≠ 0) :
    Nat.card (A ⧸ N.comap f) ∣ Nat.card (B ⧸ N) := by
  -- `f` induces a monoid homomorphism `φ` on the quotients.
  apply Subgroup.card_dvd_of_injective (QuotientGroup.map (N.comap f) N f le_rfl)
  -- Its kernel is trivial, so `φ` is injective; then Lagrange's theorem gives the divisibility.
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map]
  exact QuotientGroup.map_mk'_self (N.comap f)

end NK.GlobalCFTdeep.SecondInequality
