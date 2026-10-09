import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Audit

universe u

/-! ### Hints for the prover

There is **no** `[CharZero F]` hypothesis here, so `finrank_LTLevel_eq` and friends (which need it)
must not be used.  Argue directly:

* `LTpolyIter π 2 1 = LTpoly π 2 = X * (X + π)` (see `LubinTate/Division.lean`:
  `LTpolyIter_succ`, `LTpolyIter_zero`, and the definition of `LTpoly`), so
  `LTdivisionSet F π 2 1 = {0, -π} ⊆ F`; hence `LTLevel F π 2 1 = ⊥`
  (`IntermediateField.adjoin_le_iff`, or `IntermediateField.adjoin_le` with `⊥`).
* `normGroup F ↥(⊥ : IntermediateField F (AlgebraicClosure F)) = ⊤`: transport along an
  `F`-algebra equivalence `↥⊥ ≃ₐ[F] F` (e.g. `AlgEquiv.ofInjective (algebraMap F _) ...` or
  `IntermediateField.botEquiv`) using `NK.LocalReciprocity.normGroup_eq_of_algEquiv`, and
  `normGroup F F = ⊤` because `Algebra.norm F : F →* F` is the identity.
* RHS `= ⊤`: `NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_sup_higherUnits F π hπ 1`
  gives `Nat.card (Fˣ ⧸ (⟨π⟩ ⊔ U¹)) = (residueCard F - 1) * residueCard F ^ 0 = 1` under `hq`;
  a subgroup with index one is `⊤` (`Subgroup.index_eq_one`, or `Subgroup.eq_top_of_index_eq_one`). -/

/-- The level-one Lubin–Tate level over a field of residue cardinality two is the base field:
`f^{(1)} = πX + X² = X(X+π)` splits over `F`, so `Λ₁ = {0, -π} ⊆ F`. -/
theorem ltLevel_two_one_eq_bot (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (π : Fˣ) :
    NK.LocalReciprocityLubinTate.LTLevel F (π : F) 2 1 = ⊥ := by
  rw [NK.LocalReciprocityLubinTate.LTLevel]
  apply le_antisymm _ bot_le
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rw [NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff (π : F) 2 1 (by norm_num)] at hx
  have hpoly : NK.LocalReciprocityLubinTate.LTpolyIter (π : F) 2 1 =
      Polynomial.C (π : F) * Polynomial.X + Polynomial.X ^ 2 := by
    rw [NK.LocalReciprocityLubinTate.LTpolyIter_succ,
      NK.LocalReciprocityLubinTate.LTpolyIter_zero, Polynomial.X_comp,
      NK.LocalReciprocityLubinTate.LTpoly]
  rw [hpoly] at hx
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X] at hx
  change x ∈ Set.range (algebraMap F (AlgebraicClosure F))
  have hfac : x * ((algebraMap F (AlgebraicClosure F)) (π : F) + x) = 0 := by
    have : (algebraMap F (AlgebraicClosure F)) (π : F) * x + x ^ 2
        = x * ((algebraMap F (AlgebraicClosure F)) (π : F) + x) := by ring
    rw [← this]; exact hx
  rcases mul_eq_zero.mp hfac with h0 | hyx
  · exact ⟨0, by rw [map_zero, h0]⟩
  · refine ⟨-(π : F), ?_⟩
    rw [map_neg]
    rw [show ((algebraMap F (AlgebraicClosure F)) (π : F)) = -x from
      eq_neg_of_add_eq_zero_left hyx]
    exact neg_neg x

/-- The norm group of the bottom subextension is everything: `N_{F/F} Fˣ = Fˣ`. -/
theorem normGroup_bot_eq_top (F : Type u) [Field F] :
    NK.LocalReciprocity.normGroup F
      ↥(⊥ : IntermediateField F (AlgebraicClosure F)) = ⊤ := by
  rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv
    (IntermediateField.botEquiv F (AlgebraicClosure F))]
  rw [NK.LocalReciprocity.normGroup_eq_range, Algebra.norm_self, Units.map_id]
  exact MonoidHom.range_eq_top.mpr fun x => ⟨x, rfl⟩

theorem hondaReciprocity_level_one_residueCard_two (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (π : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (π : F))
    (hq : NK.LocalReciprocityLubinTate.residueCard F = 2) :
    NK.LocalReciprocity.normGroup F
        ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F) 2 1) =
      Subgroup.zpowers π ⊔ NK.LocalReciprocityLubinTate.higherUnits F 1 := by
  have hL : NK.LocalReciprocity.normGroup F
      ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F) 2 1) = ⊤ := by
    rw [ltLevel_two_one_eq_bot F π]
    exact normGroup_bot_eq_top F
  have hR : (Subgroup.zpowers π ⊔ NK.LocalReciprocityLubinTate.higherUnits F 1) = ⊤ := by
    have hcard := NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_sup_higherUnits
      F π hπ 1 le_rfl
    rw [hq] at hcard
    have hidx : (Subgroup.zpowers π ⊔
        NK.LocalReciprocityLubinTate.higherUnits F 1).index = 1 := by
      rw [Subgroup.index_eq_card, hcard]
      norm_num
    exact Subgroup.index_eq_one.mp hidx
  rw [hL, hR]

end NK.LocalReciprocityLubinTate.Audit
