import Mathlib
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.NumberTheory.NumberField.Completion.H2_units_ringOfIntegers_unramified
import Submission.NK.GlobalCFTdeep.Herbrand.localUnitsUnitsEquiv
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_zero_of_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

theorem hZero_localUnitSubRep_of_ramificationIdx_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) = 1 := by
  classical
  have hq : q.asIdeal.LiesOver Q.asIdeal := inferInstance
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulDistribMulAction ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))
      ↥(Place.localUnits L (Place.ofFinite q)) :=
    instMulDistribMulActionLocalUnitsSubtype (K := K) (L := L) (Place.ofFinite q)
  letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  haveI hfint : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  -- Step 1: `localUnitsUnitsEquiv` intertwines the two actions
  have hψ : ∀ (σ : ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)))
      (u : ↥(Place.localUnits L (Place.ofFinite q))),
      localUnitsUnitsEquiv q (σ • u) =
        (decompositionSubgroupIsoLocalGalois Q q hq σ) • (localUnitsUnitsEquiv q u) := by
    intro σ u
    exact localUnitsUnitsEquiv_rep (K := K) (L := L) Q q hq σ u
  -- Step 2: transport `Ĥ⁰` of the local units to the local representation
  have htrans : Nat.card (tateCohomology
        (localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) 0)
      = Nat.card (tateCohomology (Rep.of
          (Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)) 0) := by
    have h0 := natCard_tateCohomology_zero_of_mulEquiv
      (G := ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)))
      (H := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (M := ↥(Place.localUnits L (Place.ofFinite q)))
      (N := (↥(q.adicCompletionIntegers L))ˣ)
      (decompositionSubgroupIsoLocalGalois Q q hq) (localUnitsUnitsEquiv q) hψ
    exact h0
  -- Step 3: the local computation, `|Ĥ⁰(Γ, 𝒪_qˣ)| = 1` in the unramified case
  have hloc : Nat.card (tateCohomology (Rep.of
        (Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)) 0) = 1 := by
    haveI hcyc : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
        Q q hq hunr
    letI : CommGroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      IsCyclic.commGroup
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator
      (α := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
    have hper := Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
      g hg (Rep.of (Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq))
    have hsub : Subsingleton (groupCohomology (Rep.of
        (Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)) 2) :=
      Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_two_adicIntegersUnits_of_ramificationIdx_eq_one
        Q q hq hunr
    haveI : Subsingleton (groupCohomology (Rep.of
        (Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)) 2) := hsub
    have h2 : Nat.card (groupCohomology (Rep.of
        (Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)) 2) = 1 :=
      Nat.card_unique
    rw [← hper, h2]
  rw [NK.GlobalCFTdeep.hZero_def, htrans, hloc]

end NK.GlobalCFTdeep.Herbrand
