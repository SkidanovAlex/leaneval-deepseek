import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.RamificationDeep.algebra_isIntegral_comap
import Submission.NK.RamificationDeep.isIntegralClosure_comap
import Submission.NK.RamificationDeep.isNoetherianRing_comap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.RamificationDeep

/-! ## Finiteness of `A` over `A ∩ K`

The integral closure of the Noetherian integrally closed domain `𝔬 = A ∩ K` in the finite
separable extension `L` is finite over `𝔬`; here `A` *is* that integral closure, because `A` is
Galois stable (`hA`). -/

private lemma moduleFinite_comap_baseRing {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] [IsGalois K L]
    [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤) :
    Module.Finite ↥(A.comap (algebraMap K L)) ↥A := by
  haveI hfd : FiniteDimensional K L := finiteDimensional_of_isGalois A hA
  have hInt : Algebra.IsIntegral ↥(A.comap (algebraMap K L)) ↥A :=
    algebra_isIntegral_comap A hA
  haveI hIC : IsIntegralClosure ↥A ↥(A.comap (algebraMap K L)) L :=
    isIntegralClosure_comap A hInt
  haveI hNoeth : IsNoetherianRing ↥(A.comap (algebraMap K L)) :=
    isNoetherianRing_comap A
  exact IsIntegralClosure.finite ↥(A.comap (algebraMap K L)) K L ↥A

/-! ## The inclusion `A ∩ K → A ∩ E` and the transfer of finiteness

For an intermediate field `K ⊆ E ⊆ L`, the subring `A ∩ E` of `A` contains `A ∩ K`, so a finite
generating set of `A` over `A ∩ K` is also a finite generating set over `A ∩ E`:
`A ∩ K ⊆ A ∩ E` shows `(A ∩ K)·aᵢ ⊆ (A ∩ E)·aᵢ`.  This is
`Module.Finite.of_restrictScalars_finite`. -/

/-- The inclusion `A ∩ K → A ∩ E`, for `K ⊆ E ⊆ L`; both are subrings of `A`. -/
private def comapBaseHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (E : IntermediateField K L) :
    ↥(A.comap (algebraMap K L)) →+* ↥(A.comap (algebraMap ↥E L)) where
  toFun c :=
    ⟨algebraMap K ↥E (c : K), by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply K ↥E L]
      exact (ValuationSubring.mem_comap).mp c.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
private theorem comapBaseHom_coe {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (E : IntermediateField K L)
    (c : ↥(A.comap (algebraMap K L))) :
    ((comapBaseHom A E c : ↥(A.comap (algebraMap ↥E L))) : ↥E) = algebraMap K ↥E (c : K) :=
  rfl

private lemma moduleFinite_of_comap_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] (E : IntermediateField K L)
    (h : Module.Finite ↥(A.comap (algebraMap K L)) ↥A) :
    Module.Finite ↥(A.comap (algebraMap ↥E L)) ↥A := by
  letI : Algebra ↥(A.comap (algebraMap K L)) ↥(A.comap (algebraMap ↥E L)) :=
    (comapBaseHom A E).toAlgebra
  haveI : IsScalarTower ↥(A.comap (algebraMap K L)) ↥(A.comap (algebraMap ↥E L)) ↥A :=
    IsScalarTower.of_algebraMap_eq fun c => by
      have hc : algebraMap ↥(A.comap (algebraMap K L)) ↥(A.comap (algebraMap ↥E L)) c
          = comapBaseHom A E c := rfl
      rw [hc]
      apply Subtype.ext
      simp only [comapBaseHom_coe, comapHom_apply, algebraMap_comap_apply]
      exact IsScalarTower.algebraMap_apply K ↥E L (c : K)
  haveI := h
  exact Module.Finite.of_restrictScalars_finite ↥(A.comap (algebraMap K L))
    ↥(A.comap (algebraMap ↥E L)) ↥A

theorem moduleFinite_inertiaField_comap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsGalois K L] [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤) :
    Module.Finite ↥(A.comap (algebraMap ↥(NK.RamificationDeep.inertiaField (K := K) A) L)) ↥A :=
  moduleFinite_of_comap_le A (NK.RamificationDeep.inertiaField (K := K) A)
    (moduleFinite_comap_baseRing A hA)

end NK.RamificationDeep
