import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.HassePrinciple.hbnIdele
import Submission.NK.HassePrinciple.locUnits_compatible
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation
open NK.GlobalCFT

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NK.HassePrinciple

/-- **The relative Hasse–Brauer–Noether theorem from the licensed cyclic input**: the localisation
`H²(Gal(L/K), Lˣ) → ∏_w H²(Γ_w, L_wˣ)` has trivial kernel. -/
theorem hbnUnits_of_cyclicInput (h : CyclicHasseInput) {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    HBNUnits K L := by
  intro a ha
  -- the idèle localisation of the image of `a` vanishes at every place
  have hcomp := locUnits_compatible (K := K) (L := L)
  have hb : ∀ w : Place L, (ideleLoc K L w).hom ((unitsToIdeleH2 K L).hom a) = 0 := by
    intro w
    rw [← hcomp w a]
    exact ha w
  -- Shapiro for the idèles
  have hz : (unitsToIdeleH2 K L).hom a = 0 := hbnIdele (K := K) (L := L) _ hb
  -- the edge map is injective because `H¹(Γ, C_L) = 0`
  have hinj := injective_h2_units_of_subsingleton_h1_classGroupRep (K := K) (L := L)
    (subsingleton_classGroupRep_one h)
  have hinj' : Function.Injective (unitsToIdeleH2 K L).hom := by
    convert hinj using 1 <;> rfl
  refine hinj' ?_
  rw [hz, map_zero]

/-- **The relative Hasse–Brauer–Noether theorem at every finite Galois extension of number
fields, from the licensed cyclic input.**  This is the classical theorem in the finite case, and
with `NK.HassePrinciple.fieldAxiom_of_cyclicHasseInput` it is the way in which the licensed
cyclic input (`NK.HassePrinciple.CyclicHasseInput`) is consumed by the chapter: it is *not* an
input of the reduction to `NK.BrauerHasse.Sha2Vanishing` (README §22). -/
theorem hbnUnits_from_cyclicInput (h : CyclicHasseInput) {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    HBNUnits F E :=
  hbnUnits_of_cyclicInput h

end NK.HassePrinciple
