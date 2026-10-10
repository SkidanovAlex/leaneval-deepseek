import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
import Submission.Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.NK.Mine.Generation
import Submission.NeukirchUchida.Local.Transitivity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the generation of the absolute Galois group by decomposition groups

This file collects the definitions and re-exports used by
`NK.FieldTheory.Galois.stabilizer_iSup_eq_top`, namely the decomposition subgroup of a finite
place of a finite Galois extension of number fields, and the facts that the finite places of an
intermediate field are cut out by the places of the separable closure.
-/

open scoped NumberField Pointwise

namespace NK.FieldTheory.Galois

/-- The decomposition subgroup `D_w ≤ Gal(L/K)` of the finite place `w` of a number field `L`
over a number field `K`: the stabiliser of `w` under the natural action of `Gal(L/K)` on the
finite places of `L`. -/
noncomputable abbrev decompSubgroup {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) : Subgroup (L ≃ₐ[K] L) :=
  Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w

/-- The stabiliser of the valuation ring of a finite place is the decomposition subgroup of that
place. -/
theorem mem_stabilizer_valuationSubringAtPrime_iff_mem_decompSubgroup {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[K] L) :
    σ ∈ MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w) ↔
      σ ∈ decompSubgroup w :=
  Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
    w σ

end NK.FieldTheory.Galois
