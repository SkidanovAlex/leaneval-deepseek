import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Pointwise NumberField

namespace Commons.NumberTheory.NumberField.Completion

theorem isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGal : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  haveI : PerfectField Q.asIdeal.ResidueField :=
    Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum Q
  haveI hlies : q.asIdeal.LiesOver Q.asIdeal := hq
  -- The inertia subgroup of the decomposition group is trivial.
  have hcard : Nat.card (q.asIdeal.inertia Gal(L/K)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) Q.asIdeal q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal q.asIdeal Gal(L/K)]
    exact h1
  haveI hsub : Subsingleton (q.asIdeal.inertia Gal(L/K)) := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hinertia_bot : q.asIdeal.inertia Gal(L/K) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    have h : (⟨σ, hσ⟩ : ↥(q.asIdeal.inertia Gal(L/K))) = 1 := Subsingleton.elim _ _
    simpa using congrArg Subtype.val h
  have hstab_inertia_bot : q.asIdeal.inertia (MulAction.stabilizer Gal(L/K) q.asIdeal) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    apply Subtype.ext
    have h2 : (σ : Gal(L/K)) ∈ q.asIdeal.inertia Gal(L/K) := Ideal.coe_mem_inertia.mpr hσ
    rw [hinertia_bot] at h2
    simpa using h2
  have hker : (Ideal.Quotient.stabilizerHom q.asIdeal Q.asIdeal Gal(L/K)).ker = ⊥ := by
    rw [Ideal.Quotient.ker_stabilizerHom, hstab_inertia_bot]
  have hinj : Function.Injective (Ideal.Quotient.stabilizerHom q.asIdeal Q.asIdeal Gal(L/K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  -- The residue field extension is an extension of finite fields, hence has cyclic Galois group.
  haveI : Q.asIdeal.IsMaximal := inferInstance
  haveI : q.asIdeal.IsMaximal := inferInstance
  letI : Field (𝓞 K ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  letI : Field (𝓞 L ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  haveI : Finite (𝓞 L ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
  letI : Algebra (𝓞 K ⧸ Q.asIdeal) (𝓞 L ⧸ q.asIdeal) := inferInstance
  haveI : IsCyclic ((𝓞 L ⧸ q.asIdeal) ≃ₐ[𝓞 K ⧸ Q.asIdeal] (𝓞 L ⧸ q.asIdeal)) := inferInstance
  have hstab_cyc : IsCyclic (MulAction.stabilizer Gal(L/K) q.asIdeal) :=
    isCyclic_of_injective _ hinj
  -- The decomposition group of `q` is the stabiliser of `q`.
  have hEq : decompositionSubgroup (K := K) q = MulAction.stabilizer Gal(L/K) q.asIdeal := by
    ext σ
    rw [mem_decompositionSubgroup_iff_smul, MulAction.mem_stabilizer_iff]
  have hdec_cyc : IsCyclic (decompositionSubgroup (K := K) q) := hEq ▸ hstab_cyc
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  exact (decompositionSubgroupMulEquivLocalGalois Q q hq).isCyclic.mp hdec_cyc

end Commons.NumberTheory.NumberField.Completion
