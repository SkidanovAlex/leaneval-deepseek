import Mathlib
import Submission.NK.FrobeniusBridge.Basic
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.NeukirchUchida.Local.PlaceFromValuation

namespace NK.FrobeniusBridge

open scoped Pointwise NumberField

set_option linter.unusedSectionVars false

/-- **A Frobenius element at a finite place stabilises that place.**  For a finite Galois
extension `L/K` of number fields and a finite place `P` of `L`, an element of `Gal(L/K)` which is
an arithmetic Frobenius at `P` lies in the decomposition group of `P`. -/
private lemma mem_decompositionSubgroup_of_isFrobAt {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)} {σ : Gal(L/K)}
    (hP : NK.Chebotarev.IsFrobAt P σ) :
    σ ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) P := by
  rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup]
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [Submission.NeukirchUchida.Local.placeSmul_asIdeal]
  exact NK.Chebotarev.IsFrobAt.map_eq_self hP

theorem mem_decompositionGroup_of_isFrobAtPlace {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    {A : NK.FrobeniusBridge.FinitePlaceOf K K'} {g : Gal(K'/K)}
    (h : NK.FrobeniusBridge.IsFrobAtPlace A g) :
    g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 := by
  set p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    Submission.NeukirchUchida.primeOf A.1 A.2 with hp
  have hA : A.1.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p := by
    rw [hp]
    exact Submission.NeukirchUchida.primeOf_spec A.1 A.2
  have hmain : g ∈ MulAction.stabilizer (Gal(K'/K)) A.1 :=
    (Submission.NeukirchUchida.Local.mem_stabilizer_iff_forall_mem_decompositionSubgroup
      (K := K) (K' := K') p A.1 hA g).mpr (by
        intro L hLfin hLnorm
        haveI : FiniteDimensional K L := hLfin
        haveI : Normal K L := hLnorm
        haveI : NumberField ↥L :=
          Submission.NeukirchUchida.Local.instNumberFieldIntermediateField L
        haveI : IsGalois K ↥L := inferInstance
        have hne : A.1.comap (algebraMap ↥L K') ≠ ⊤ :=
          NK.Reconstruct.comap_level_ne_top A.2 L
        have hplace : Submission.NeukirchUchida.Local.placeOf p A.1 hA L =
            NK.Reconstruct.primeOfLevel A.1 L hne :=
          Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
            (R := NumberField.RingOfIntegers ↥L) (K := ↥L) (by
              rw [← Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf
                    p A.1 hA L,
                ← NK.Reconstruct.primeOfLevel_spec A.1 L hne])
        refine mem_decompositionSubgroup_of_isFrobAt
          (P := Submission.NeukirchUchida.Local.placeOf p A.1 hA L) ?_
        rw [hplace]
        exact h L)
  show g ∈ MulAction.stabilizer (Gal(K'/K)) A.1
  exact hmain

end NK.FrobeniusBridge
