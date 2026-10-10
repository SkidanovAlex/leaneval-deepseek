import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer cochain of a local unit kills the inertia (node form)

`Work.SSGRoute.ZDataTwo.TwoRec.killsInertia_of_unit_notTwo`: at a finite place `B` of `Ω` where `2`
is a *unit* (`¬ B.valuation (2 : Ω) < 1`), the Kummer cochain `χ_X` of an element `X ∈ (↥K)ˣ` that
is itself a unit at `B` (`B.valuation (algebraMap ↥K Ω X) = 1`) vanishes on the inertia of `B`.

This is the `p = 2`, node-`ZMod`-cochain instance of the proved local fact
`Work.SSGRoute.kummerCharZMod_eq_zero_of_isInertia_of_unit` (the Kummer extension
`K(X^{1/2})/K` is unramified at `B` because `X` is a unit and the residue characteristic is odd),
composed with the two bridges

* `ZSplit.nodeKummerCocharZMod_apply` (the node cochain on `K.fixingSubgroup` is the descended
  Kummer character of `↥K`), and
* `ZSplit.isInertia_baseChange` (the inertia condition transports along
  `IntermediateField.fixingSubgroupEquiv`).

It is the missing input of the `hout` verification of the p.16 chain (see
`ZDataTwo/TwoRec/NOTE_diagonal_p16_plan.md`: the product formula
`ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside` is applied with a `T'` containing all
the places where `χ_X` could be ramified, and at the places outside `T'` the cochains must kill the
inertia).
-/

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem killsInertia_of_unit_notTwo {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (X : (↥K)ˣ) (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hnot2 : ¬ B.valuation (2 : Ω) < 1)
    (hunit : B.valuation (algebraMap ↥K Ω (X : ↥K)) = 1) :
    ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X u = 0 := by
  -- `↥K` is a number field with separable closure `Ω`
  haveI : IsAlgClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
  intro u hu hI
  -- the node cochain on `K.fixingSubgroup` is the descended Kummer character of `↥K`
  rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
    (β := X) hu]
  -- the local fact, at the level `↥K`
  refine Work.SSGRoute.kummerCharZMod_eq_zero_of_isInertia_of_unit k Ω K 2 (⟨ζ, hζK⟩ : ↥K)
    (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) B hnot2 X hunit
    ((IntermediateField.fixingSubgroupEquiv K) ⟨u, hu⟩) ?_
  -- the inertia condition is the same at the two levels
  exact (Work.SSGRoute.isInertia_baseChange (k := k) (Ω := Ω) (K := K) B u hu).mpr hI

end Work.SSGRoute.ZDataTwo.TwoRec
