import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite set of places whose `T`-idèles surject onto the class group

Every idèle is a local unit at all but finitely many places, and the ideal class map
`𝕀 L →* Cl(𝓞 L)` is surjective.  Since the class group of a number field is finite, a
single finite set of places `T` can be chosen so that every idèle class in `Cl(𝓞 L)` is
represented by an idèle which is a local unit outside `T` — i.e. by an element of the
`T`-idèles `𝕀_{L,T}`.

This is the input making `𝕀_{L,T}` "large enough" for the Herbrand quotient computation:
it says exactly that the natural map `𝕀_{L,T} → Cl(𝓞 L)` is onto for a suitable finite `T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-- The set of places at which an idèle is not a local unit is finite: this is the
restricted product condition defining the idèles. -/
theorem finite_setOf_not_mem_localUnits {L : Type} [Field L] [NumberField L] (x : Idele L) :
    {v : Place L | x v ∉ Place.localUnits L v}.Finite :=
  Filter.eventually_cofinite.mp x.2

theorem exists_finset_TIdeles_surjective {L : Type} [Field L] [NumberField L] :
    ∃ T : Finset (NK.GlobalCFT.Place L), ∀ c : ClassGroup (NumberField.RingOfIntegers L),
      ∃ u ∈ TIdeles ((T : Set (NK.GlobalCFT.Place L))),
        NK.GlobalCFT.IdeleClassGroup.idealClassMap L u = c := by
  classical
  -- choose one idèle representing each class of the (finite) class group
  choose u hu using fun c : ClassGroup (NumberField.RingOfIntegers L) =>
    IdeleClassGroup.idealClassMap_surjective L c
  -- the places at which one of these chosen idèles fails to be a local unit
  have hfin : (⋃ c : ClassGroup (NumberField.RingOfIntegers L),
      {v : Place L | u c v ∉ Place.localUnits L v}).Finite :=
    Set.finite_iUnion fun c => finite_setOf_not_mem_localUnits (u c)
  refine ⟨hfin.toFinset, fun c => ⟨u c, ?_, hu c⟩⟩
  rw [mem_TIdeles]
  intro w hw
  by_contra hw'
  exact hw (by
    rw [Set.Finite.coe_toFinset hfin]
    exact Set.mem_iUnion.mpr ⟨c, hw'⟩)

end NK.GlobalCFTdeep.Herbrand
