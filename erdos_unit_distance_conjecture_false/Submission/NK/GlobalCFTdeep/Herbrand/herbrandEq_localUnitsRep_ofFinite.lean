import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.LocalUnits
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_units_adicCompletion_of_abelian
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_helpers

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open scoped NumberField
open NumberField IsDedekindDomain

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFTdeep

/-- **The local Herbrand quotient of the decomposition group on the local units.** For a finite
Galois extension `L / K` of number fields, a finite place `q` of `L` above `Q`, if the
decomposition group `D_q` of `q` is commutative, then the Herbrand quotient of the local units
`L_qˣ` with the action of `D_q` is the order of `D_q`. -/
theorem herbrandEq_localUnitsRep_ofFinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    (hcomm : ∀ a b : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q), a * b = b * a) :
    NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q))
      (Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q))) := by
  classical
  have hq : q.asIdeal.LiesOver Q.asIdeal := inferInstance
  -- the local field is finite and Galois over the base local field
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  haveI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := Fintype.ofFinite _
  -- the isomorphism between the decomposition group and the local Galois group
  let e : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q) ≃*
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois Q q hq
  -- commutativity of the local Galois group, transported along `e`
  have hcommG : ∀ a b : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      a * b = b * a := by
    intro a b
    calc a * b = e (e.symm a) * e (e.symm b) := by rw [e.apply_symm_apply, e.apply_symm_apply]
      _ = e (e.symm a * e.symm b) := (e.map_mul _ _).symm
      _ = e (e.symm b * e.symm a) := by rw [hcomm]
      _ = e (e.symm b) * e (e.symm a) := e.map_mul _ _
      _ = b * a := by rw [e.apply_symm_apply, e.apply_symm_apply]
  -- the local Herbrand computation in the abelian case
  have hG := herbrandEq_units_adicCompletion_of_abelian Q q hcommG
  -- the local units representation of the decomposition group is the restriction along `e`
  have hrep := NK.GlobalCFTdeep.localUnitsRep_eq_res Q q hq
  -- transfer of the two Tate cohomology cardinalities
  have h0 : hZero (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q))
      = hZero (Rep.ofMulDistribMulAction
          (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ) := by
    rw [hrep, hZero_def, hZero_def]
    exact NK.GlobalCFTdeep.natCard_tateCohomology_zero_of_mulEquiv_res e
      (Representation.ofMulDistribMulAction
        (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ)
  have h1 : hOne (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q))
      = hOne (Rep.ofMulDistribMulAction
          (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ) := by
    rw [hrep, hOne_def, hOne_def]
    exact NK.GlobalCFTdeep.natCard_tateCohomology_one_of_mulEquiv_res e
      (Representation.ofMulDistribMulAction
        (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (q.adicCompletion L)ˣ)
  -- the order of the decomposition group is the local degree
  have hcard : Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q))
      = Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    NK.GlobalCFTdeep.natCard_decompositionSubgroup_eq_finrank Q q hq
  rw [HerbrandEq] at hG ⊢
  rw [h0, h1, hcard]
  exact hG

end NK.GlobalCFTdeep.Herbrand
