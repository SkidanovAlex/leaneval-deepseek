import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.residueActionHom_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_adicCompletion_of_residue_ringEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.NumberTheory.NumberField.Completion

theorem isCyclic_algEquiv_fixedField_inertia {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (I : Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)),
      Nat.card I = q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) →
      (∀ σ, σ ∈ I ↔ ∀ x : q.adicCompletionIntegers L,
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (σ (x : q.adicCompletion L) - (x : q.adicCompletion L)) < 1) →
      IsCyclic (↥(IntermediateField.fixedField I) ≃ₐ[Q.adicCompletion K]
        ↥(IntermediateField.fixedField I)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro I _hcard hmem
  -- The subgroup characterized by triviality on the residue field is the kernel of the action of
  -- the local Galois group on the residue field, i.e. the inertia subgroup.
  obtain ⟨ρ, hρker, hρrange⟩ := residueActionHom_adicCompletion Q q hq
  have hIker : I = ρ.ker := by
    ext σ
    exact (hmem σ).trans (hρker σ).symm
  have hInorm : I.Normal := by
    rw [hIker]
    infer_instance
  haveI := hInorm
  -- The quotient by inertia is the Galois group of the residue field extension, which is a
  -- finite extension of finite fields, hence cyclic.
  have hcycRange : IsCyclic ρ.range := by
    rw [hρrange]
    haveI : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
      finite_residueField_adicCompletion L q
    letI : Algebra (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))
        (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
      (natResidueMap Q q hq).toAlgebra
    exact (fixSubgroupMulEquiv (natResidueMap Q q hq)).isCyclic.mpr inferInstance
  have hcycQuot : IsCyclic
      ((q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) ⧸ I) := by
    have e : ((q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) ⧸ I) ≃* ρ.range :=
      (QuotientGroup.quotientMulEquivOfEq hIker).trans (QuotientGroup.quotientKerEquivRange ρ)
    exact e.isCyclic.mpr hcycRange
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  haveI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  -- The fixed field of the normal subgroup `I` is Galois over `K_Q` with group `G ⧸ I`.
  exact (IsGalois.normalAutEquivQuotient I).isCyclic.mp hcycQuot

end Commons.NumberTheory.NumberField.Completion
