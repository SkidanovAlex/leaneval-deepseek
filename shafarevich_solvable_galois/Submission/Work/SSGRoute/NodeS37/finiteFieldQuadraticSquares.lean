import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every element of a finite field of odd order is a square in any quadratic extension

This is the residue-field input of the `ρ`-fixed branch of the local dichotomy of Schmidt--Wingberg's
p. 16 computation (`ACTION_claimOfPreTwo_p16_carve_session39.md` §7 and the addendum of
`PING_node_s41_p16_representative.md`): at a `ρ`-fixed place `P` the invariant unit `a` has its
residue in the fixed residue field `κ_𝔭`, and `κ_𝔭`-elements are squares in the quadratic residue
extension `κ_P` — so Hensel makes `a` a square in the completion.

The statement is the exact arithmetic content: for a finite field `F` of odd order (`Odd
(Fintype.card F)`) and a quadratic extension `E/F` (`Module.finrank F E = 2`) of odd residue
characteristic (`ringChar E ≠ 2`), every element of `F` is a square in `E`.

The proof is Euler's criterion (`FiniteField.isSquare_iff`): for `a ≠ 0`,
`(algebraMap F E a) ^ (Fintype.card E / 2) = 1` because `Fintype.card E = (Fintype.card F) ^ 2`,
`Fintype.card E / 2 = (Fintype.card F - 1) * ((Fintype.card F + 1) / 2)` (`Fintype.card F` being odd)
and `(algebraMap F E a) ^ (Fintype.card F - 1) = 1` (Fermat in `F`, transported along `algebraMap`).
-/

namespace Work.SSGRoute.NodeS37

/-- **Every element of a finite field of odd order is a square in any quadratic extension.** -/
theorem isSquare_algebraMap_of_finrank_two {F E : Type*} [Field F] [Fintype F] [Field E]
    [Algebra F E] [FiniteDimensional F E] [Fintype E]
    (h2 : Module.finrank F E = 2) (hchar : ringChar E ≠ 2) (hodd : Odd (Fintype.card F))
    (a : F) :
    IsSquare (algebraMap F E a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by simp⟩
  have hane : algebraMap F E a ≠ 0 := fun h =>
    ha (FaithfulSMul.algebraMap_injective F E (by simpa using h))
  rw [FiniteField.isSquare_iff hchar hane]
  -- the cardinality of `E` is the square of the cardinality of `F`
  have hcardE : Fintype.card E = (Fintype.card F) ^ 2 := by
    have e : E ≃ (Fin (Module.finrank F E) → F) :=
      (Module.finBasis F E).equivFun
    rw [h2] at e
    rw [Fintype.card_congr e, Fintype.card_fun]
    simp
  -- Fermat in `F`, transported along `algebraMap`
  have hfermat : (algebraMap F E a) ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]
  obtain ⟨k, hk⟩ := hodd
  have hk1 : Fintype.card F - 1 = 2 * k := by omega
  have hk2 : Fintype.card F + 1 = 2 * (k + 1) := by omega
  have hEm : Fintype.card E = 2 * (2 * (k * k) + 2 * k) + 1 := by rw [hcardE, hk]; ring
  have hdiv : Fintype.card E / 2 =
      (Fintype.card F - 1) * ((Fintype.card F + 1) / 2) := by
    rw [hEm, hk1, hk2, Nat.mul_add_div (by norm_num : 0 < 2),
      Nat.div_eq_of_lt (by norm_num : 1 < 2), add_zero]
    have : (2 * (k + 1)) / 2 = k + 1 := by omega
    rw [this]; ring
  rw [hdiv, pow_mul, hfermat, one_pow]

end Work.SSGRoute.NodeS37
