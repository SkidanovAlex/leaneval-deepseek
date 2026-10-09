/-
Copyright (c) 2025. All rights reserved.

# Products of realizable groups of coprime order

Realizability over `ℚ` (or any field `F`) is closed under forming products of groups of
**coprime order**: if `G` and `H` are realizable over `F` and `Nat.card G` is coprime to
`Nat.card H`, then `G × H` is realizable over `F`.  The reason is that two realizations of
`G` and `H` inside a common algebraic closure intersect in a subextension whose Galois group
is a quotient of both, hence of order dividing `gcd (Nat.card G) (Nat.card H) = 1`; so the
intersection is the base field and the compositum is linearly disjoint, and
`Work.FieldTheory.gal_sup_prod` computes its Galois group.

Together with `Submission/Abelian.lean` (every finite abelian group is realizable over `ℚ`)
and `Submission/Crossing.lean` (products with finite abelian groups) this gives more
unconditional realizability statements: e.g. `G × S₃` is realizable over `ℚ` for every
realizable `G` with `Nat.card G` coprime to `6`, and a product of realizable groups of
pairwise coprime order is realizable.

The main technical input is `finrank` divisibility for a subextension
(`IntermediateField.finrank_bot_mul_relfinrank`): for finite Galois `L/F`, the Galois group
of `L` has cardinality `[L : F]` (`IsGalois.card_aut_eq_finrank`).
-/
import Mathlib
import Submission.Realization
import Submission.Combine
import Submission.Work.FieldTheory.gal_sup_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

universe u

open scoped Classical

/-! ## The intersection of two realizations of coprime order is the base field -/

/-- If `L` and `M` are finite Galois subextensions of `Ω/F` whose Galois groups are `G` and `H`
with `Nat.card G` and `Nat.card H` coprime, then `L ⊓ M = ⊥`.  (The Galois group of the
intersection is a quotient of both `G` and `H`, hence trivial.) -/
theorem inf_eq_bot_of_coprime_card {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {G H : Type*} [Group G] [Group H]
    (L M : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F M] [IsGalois F M]
    (eL : G ≃* (L ≃ₐ[F] L)) (eM : H ≃* (M ≃ₐ[F] M))
    (hcop : (Nat.card G).Coprime (Nat.card H)) : L ⊓ M = ⊥ := by
  have hcardL : Nat.card (L ≃ₐ[F] L) = Nat.card G := Nat.card_congr eL.toEquiv.symm
  have hcardM : Nat.card (M ≃ₐ[F] M) = Nat.card H := Nat.card_congr eM.toEquiv.symm
  have hdvdL : Nat.card (↥(L ⊓ M) ≃ₐ[F] ↥(L ⊓ M)) ∣ Nat.card G := by
    rw [← hcardL, IsGalois.card_aut_eq_finrank F L, IsGalois.card_aut_eq_finrank F ↥(L ⊓ M)]
    exact ⟨_, (IntermediateField.finrank_bot_mul_relfinrank inf_le_left).symm⟩
  have hdvdM : Nat.card (↥(L ⊓ M) ≃ₐ[F] ↥(L ⊓ M)) ∣ Nat.card H := by
    rw [← hcardM, IsGalois.card_aut_eq_finrank F M, IsGalois.card_aut_eq_finrank F ↥(L ⊓ M)]
    exact ⟨_, (IntermediateField.finrank_bot_mul_relfinrank inf_le_right).symm⟩
  have hgcd : (Nat.card G).gcd (Nat.card H) = 1 := hcop
  have hone : Nat.card (↥(L ⊓ M) ≃ₐ[F] ↥(L ⊓ M)) = 1 :=
    Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hdvdL hdvdM)
  have hfin : Module.finrank F ↥(L ⊓ M) = 1 := by
    rw [← IsGalois.card_aut_eq_finrank F ↥(L ⊓ M), hone]
  exact IntermediateField.finrank_eq_one_iff.mp hfin

/-! ## The product theorem -/

/-- **A product of two realizable groups of coprime order is realizable.** -/
theorem realizableOver_prod_of_coprime_card {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (hG : RealizableOver ℚ G) (hH : RealizableOver ℚ H)
    (hcop : (Nat.card G).Coprime (Nat.card H)) : RealizableOver ℚ (G × H) := by
  obtain ⟨L, hLfd, hLG, ⟨eL⟩⟩ := hG.toClosure
  obtain ⟨M, hMfd, hMG, ⟨eM⟩⟩ := hH.toClosure
  have hbot : L ⊓ M = ⊥ :=
    @inf_eq_bot_of_coprime_card ℚ (AlgebraicClosure ℚ) _ _ _ G H _ _ L M
      hLfd hLG hMfd hMG eL eM hcop
  have h := realizableOver_prod_of_inf_eq_bot_closure L M hLfd hLG hMfd hMG hbot
  exact h.of_mulEquiv (MulEquiv.prodCongr eL eM).symm

end Submission
