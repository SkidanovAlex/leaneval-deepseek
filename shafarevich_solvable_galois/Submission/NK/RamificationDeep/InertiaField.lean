import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.RamificationDeep.Defs
import Submission.NK.Ramification.ramificationSubgroup_succ_eq_of_uniformizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace NK.RamificationDeep

universe u

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The valuation ring of an intermediate field.**  `A ∩ E` as a valuation subring of `E`. -/
noncomputable def restrictRing (A : ValuationSubring L) (E : IntermediateField K L) :
    ValuationSubring ↥E :=
  A.comap (algebraMap ↥E L)

@[simp]
theorem mem_restrictRing_iff (A : ValuationSubring L) (E : IntermediateField K L) (x : ↥E) :
    x ∈ restrictRing A E ↔ (x : L) ∈ A := Iff.rfl

/-- The inclusion `A ∩ E → A`.  (Used to express "the coefficients lie in `A`".) -/
noncomputable def restrictRingToA (A : ValuationSubring L) (E : IntermediateField K L) :
    ↥(restrictRing A E) →+* A where
  toFun b := ⟨(b : ↥E), b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem restrictRingToA_coe (A : ValuationSubring L) (E : IntermediateField K L)
    (b : ↥(restrictRing A E)) :
    ((restrictRingToA A E b : A) : L) = (b : ↥E) := rfl

/-- The inertia subgroup of `A`, viewed inside `Gal(L/K)` (the decomposition subgroup is already a
subgroup of `Gal(L/K)`). -/
noncomputable def inertiaImage (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (Subgroup.subtype (A.decompositionSubgroup K))

/-- **The inertia field.**  For a valuation subring `A` of `L` over a base field `K`, this is the
fixed field of the inertia subgroup `G_0 = A.inertiaSubgroup K`, viewed inside `Gal(L/K)`.

This is the field `E` of the uniformizer criterion (Serre, *Local Fields*, IV §2): it is pointwise
fixed by `G_0`, and it is the largest intermediate field `K ⊆ E ⊆ L` with this property. -/
noncomputable def inertiaField (A : ValuationSubring L) : IntermediateField K L :=
  IntermediateField.fixedField (inertiaImage (K := K) A)

@[simp]
theorem inertiaField_eq_fixedField_inertiaImage (A : ValuationSubring L) :
    inertiaField (K := K) A = IntermediateField.fixedField (inertiaImage (K := K) A) := rfl

section Setup

variable (A : ValuationSubring L) [IsDiscreteValuationRing A] [IsGalois K L]

/-- The Galois group `Gal(L/K)` is finite as soon as the decomposition subgroup is: it equals the
whole group by hypothesis. -/
theorem finite_galoisGroup (hA : A.decompositionSubgroup K = ⊤)
    [Finite ↥(A.decompositionSubgroup K)] : Finite (L ≃ₐ[K] L) := by
  have : Finite ↥(⊤ : Subgroup (L ≃ₐ[K] L)) := hA ▸ inferInstance
  exact Finite.of_equiv _ (Subgroup.topEquiv (G := (L ≃ₐ[K] L))).toEquiv

/-- In the situation of the uniformizer data, `L/K` is a finite Galois extension. -/
theorem finiteDimensional_of_isGalois (hA : A.decompositionSubgroup K = ⊤)
    [Finite ↥(A.decompositionSubgroup K)] : FiniteDimensional K L := by
  haveI := finite_galoisGroup A hA
  exact IsGalois.finiteDimensional_of_finite K L

end Setup

end NK.RamificationDeep
