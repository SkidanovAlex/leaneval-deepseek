import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalReciprocity.LocalSetup

open scoped NumberField

namespace NK.LocalReciprocity

theorem exists_isFrobeniusLocal {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    ∃ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      NK.LocalReciprocity.IsFrobeniusLocal Q q σ := by
  classical
  let ResK := IsLocalRing.ResidueField (Q.adicCompletionIntegers K)
  let ResL := IsLocalRing.ResidueField (q.adicCompletionIntegers L)
  let ψ : ResK →+* ResL := Commons.NumberTheory.NumberField.Completion.natResidueMap Q q hq
  letI : Algebra ResK ResL := ψ.toAlgebra
  haveI hFinK : Finite ResK :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K Q
  haveI hFinL : Finite ResL :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
  haveI : Fintype ResK := Fintype.ofFinite ResK
  haveI : Module.Finite ResK ResL := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic ResK ResL := Algebra.IsAlgebraic.of_finite ResK ResL
  let F : ResL ≃ₐ[ResK] ResL := FiniteField.frobeniusAlgEquivOfAlgebraic ResK ResL
  let τ : ResL ≃+* ResL := F.toRingEquiv
  have hcardK : Fintype.card ResK = residueCard K Q :=
    (Nat.card_eq_fintype_card (α := ResK)).symm
  have hτcoe : ∀ y : ResL, τ y = y ^ residueCard K Q := by
    intro y
    show F y = y ^ residueCard K Q
    rw [show (F : ResL → ResL) = fun y => y ^ Fintype.card ResK from
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic ResK ResL, hcardK]
  have hτfix : ∀ a : ResK, τ (ψ a) = ψ a := by
    intro a
    have h := F.commutes a
    rw [RingHom.algebraMap_toAlgebra ψ] at h
    exact h
  obtain ⟨σ, hσfix, hσres⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_adicCompletion_of_residue_ringEquiv
      Q q hq ψ (Commons.NumberTheory.NumberField.Completion.natResidueMap_injective Q q hq) τ hτfix
  let σ' : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L :=
    AlgEquiv.ofRingEquiv (f := σ) (fun y => by
      rw [RingHom.algebraMap_toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)]
      exact hσfix y)
  refine ⟨σ', ?_⟩
  intro x
  have hσx : σ (x : q.adicCompletion L) ∈ q.adicCompletionIntegers L :=
    (Commons.NumberTheory.NumberField.Completion.algEquiv_mem_adicCompletionIntegers_iff_adicCompletion
      Q q hq σ' (x : q.adicCompletion L)).mpr x.2
  have hxN : (x : q.adicCompletion L) ^ residueCard K Q ∈ q.adicCompletionIntegers L :=
    pow_mem x.2 _
  have hsub : σ (x : q.adicCompletion L) - (x : q.adicCompletion L) ^ residueCard K Q ∈
      q.adicCompletionIntegers L := sub_mem hσx hxN
  have hres_eq : IsLocalRing.residue (q.adicCompletionIntegers L)
        ⟨σ (x : q.adicCompletion L), hσx⟩
      = (IsLocalRing.residue (q.adicCompletionIntegers L) x) ^ residueCard K Q := by
    rw [← hσres x hσx]
    exact hτcoe _
  have hmem : (⟨σ (x : q.adicCompletion L) - (x : q.adicCompletion L) ^ residueCard K Q, hsub⟩ :
      q.adicCompletionIntegers L) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    refine (IsLocalRing.residue_eq_zero_iff (R := q.adicCompletionIntegers L) _).mp ?_
    have h1 : (⟨σ (x : q.adicCompletion L) - (x : q.adicCompletion L) ^ residueCard K Q, hsub⟩ :
        q.adicCompletionIntegers L) = ⟨σ (x : q.adicCompletion L), hσx⟩ - x ^ residueCard K Q := by
      ext
      simp
    rw [h1, map_sub, map_pow, hres_eq, sub_self]
  have hval :=
    (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
      q ⟨σ (x : q.adicCompletion L) - (x : q.adicCompletion L) ^ residueCard K Q, hsub⟩).mp hmem
  have hcoe : (σ' : q.adicCompletion L → q.adicCompletion L) = ⇑σ := rfl
  simpa only [show σ' (x : q.adicCompletion L) = σ (x : q.adicCompletion L) from
    congrFun hcoe (x : q.adicCompletion L)] using hval

end NK.LocalReciprocity
