import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.CharBridge

namespace Work.BG

/-- `|K : C_K(g)|` equals the cardinality of the conjugacy class of `g`, stated as the
`Nat.card` of the subtype of elements `x` with `ConjClasses.mk x = ConjClasses.mk g`
(the form in which the class size appears in `isIntegral_card_mul_character_div`). -/
theorem centralizer_index_eq_natCard_conjClass {K : Type*} [Group K] (g : K) :
    (Subgroup.centralizer ({g} : Set K)).index =
      Nat.card { x : K // ConjClasses.mk x = ConjClasses.mk g } := by
  rw [Subgroup.index_centralizer_eq_ncard]
  rw [← Nat.card_coe_set_eq (conjugatesOf g)]
  refine Nat.card_congr (Set.equivOfEq ?_)
  ext x
  change IsConj g x ↔ ConjClasses.mk x = ConjClasses.mk g
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **X3.** `|K : C_K(g)| · χ(g) / χ(1)` is an algebraic integer for every irreducible
character `χ` (Gorenstein 4.2.10, value form).  The input is
`OddOrder.RepresentationTheory.isIntegral_card_mul_character_div` (the class-size
`|C| · χ_ρ(g) / χ_ρ(1)` form) together with `centralizer_index_eq_natCard_conjClass`,
which identifies the class size with the centralizer index. -/
theorem centralIntegral : Work.GW2.C16.CentralIntegralProp := by
  intro K _ _ χ hχ g
  obtain ⟨V, hV1, hV2, hV3, ρ, hρ, hχeq⟩ := hχ
  letI := hV1
  letI := hV2
  letI := hV3
  rw [centralizer_index_eq_natCard_conjClass g]
  rw [hχeq]
  exact isIntegral_card_mul_character_div ρ (ConjClasses.mk g) rfl

end Work.BG
