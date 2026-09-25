import Mathlib
import Submission.NK.Summary.NUV2.Tame.Prelude
import Submission.NK.NUV2.TamePrimeLevel.normGroup_ne_of_finrank_eq_prime_tame
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
import Submission.Commons.FieldTheory.SeparableClosure.nonempty_algHom_of_isSepClosure
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg

set_option linter.style.haveILetI false

namespace NK.Summary.NUV2.Tame

open IsDedekindDomain

/-- In a cyclic group the multiplication is commutative. -/
lemma mul_comm_of_isCyclic {G : Type*} [Group G] (h : IsCyclic G) (a b : G) : a * b = b * a := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨m, rfl⟩ := hg a
  obtain ⟨n, rfl⟩ := hg b
  rw [← zpow_add, ← zpow_add, add_comm]

/-- A finite Galois extension of the local completion at a finite place, of prime degree `ℓ`, is
`F`-isomorphic to a finite normal level of the maximal abelian subextension of a separable
closure, with the same norm group. -/
theorem exists_maxAbelianSubext_level {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type} [Field B] [Algebra (Q.adicCompletion K) B]
    [FiniteDimensional (Q.adicCompletion K) B] [IsGalois (Q.adicCompletion K) B]
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfin : Module.finrank (Q.adicCompletion K) B = ℓ) :
    ∃ L : IntermediateField (Q.adicCompletion K)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
          (SeparableClosure (Q.adicCompletion K))),
      Nonempty (B ≃ₐ[Q.adicCompletion K] ↥L) ∧
      FiniteDimensional (Q.adicCompletion K) ↥L ∧
      Normal (Q.adicCompletion K) ↥L ∧
      Module.finrank (Q.adicCompletion K) ↥L = ℓ ∧
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) B =
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L := by
  haveI hsep : Algebra.IsSeparable (Q.adicCompletion K) B := inferInstance
  obtain ⟨φ⟩ := Commons.FieldTheory.SeparableClosure.nonempty_algHom_of_isSepClosure
    (F := Q.adicCompletion K) (F' := B) (E := SeparableClosure (Q.adicCompletion K))
  let L' : IntermediateField (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)) :=
    φ.fieldRange
  have e₁ : B ≃ₐ[Q.adicCompletion K] ↥L' := AlgEquiv.ofInjective φ φ.injective
  haveI hfdL' : FiniteDimensional (Q.adicCompletion K) ↥L' :=
    FiniteDimensional.of_surjective e₁.toLinearMap e₁.surjective
  haveI hgalL' : IsGalois (Q.adicCompletion K) ↥L' := IsGalois.of_algEquiv e₁
  haveI hnormL' : Normal (Q.adicCompletion K) ↥L' := Normal.of_algEquiv e₁
  have hcardL' : Nat.card (↥L' ≃ₐ[Q.adicCompletion K] ↥L') = ℓ := by
    rw [IsGalois.card_aut_eq_finrank]
    exact (e₁.toLinearEquiv.finrank_eq).symm.trans hfin
  have hcommL' : ∀ σ τ : ↥L' ≃ₐ[Q.adicCompletion K] ↥L', σ * τ = τ * σ := by
    intro σ τ
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    exact mul_comm_of_isCyclic (isCyclic_of_prime_card hcardL') σ τ
  have hle : L' ≤ NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) :=
    NK.LocalReciprocity.le_maxAbelianSubext_of_commutative L' hcommL'
  let A := NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
    (SeparableClosure (Q.adicCompletion K))
  let L : IntermediateField (Q.adicCompletion K) A :=
    IntermediateField.comap (IntermediateField.val A) L'
  have hmap : L.map (IntermediateField.val A) = L' :=
    IntermediateField.map_comap_eq_self (f := IntermediateField.val A)
      (by rwa [IntermediateField.fieldRange_val])
  let e₂ : ↥L ≃ₐ[Q.adicCompletion K] ↥L' :=
    { toFun := fun x => ⟨(IntermediateField.val A) x.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hle y.2⟩, by
        show (IntermediateField.val A) ⟨y.1, hle y.2⟩ ∈ L'
        simpa using y.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext (Subtype.ext rfl)
      map_add' := fun x y => Subtype.ext (Subtype.ext rfl)
      commutes' := fun c => Subtype.ext (Subtype.ext rfl) }
  refine ⟨L, ⟨e₁.trans e₂.symm⟩, ?_, ?_, ?_, ?_⟩
  · exact FiniteDimensional.of_surjective e₂.symm.toLinearMap e₂.symm.surjective
  · exact Normal.of_algEquiv e₂.symm
  · exact ((e₂.trans e₁.symm).toLinearEquiv.finrank_eq).trans hfin
  · exact NK.LocalReciprocity.normGroup_eq_of_algEquiv (e₁.trans e₂.symm)

theorem nonempty_algEquiv_of_inertiaDeg_eq_one {K : Type} [Field K] [NumberField K]
    {L₁ : Type} [Field L₁] [NumberField L₁] [Algebra K L₁] [FiniteDimensional K L₁] [IsGalois K L₁]
    {L₂ : Type} [Field L₂] [NumberField L₂] [Algebra K L₂] [FiniteDimensional K L₂] [IsGalois K L₂]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (hq₁ : q₁.asIdeal.LiesOver Q.asIdeal)
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₂ : q₂.asIdeal.LiesOver Q.asIdeal)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (hunram : IsUnit ((ℓ : ℕ) : Q.adicCompletionIntegers K))
    (hdeg₁ : q₁.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q₁.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = ℓ)
    (hdeg₂ : q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = ℓ)
    (hf₁ : q₁.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1)
    (hf₂ : q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q₁ hq₁)
    letI : Algebra (Q.adicCompletion K) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q₂ hq₂)
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q₁.adicCompletion L₁) =
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q₂.adicCompletion L₂) →
      Nonempty ((q₁.adicCompletion L₁) ≃ₐ[Q.adicCompletion K] (q₂.adicCompletion L₂)) := by
  intro hN
  haveI hfd₁ : FiniteDimensional (Q.adicCompletion K) (q₁.adicCompletion L₁) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q₁ hq₁
  haveI hfd₂ : FiniteDimensional (Q.adicCompletion K) (q₂.adicCompletion L₂) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q₂ hq₂
  haveI hgal₁ : IsGalois (Q.adicCompletion K) (q₁.adicCompletion L₁) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q₁ hq₁
  haveI hgal₂ : IsGalois (Q.adicCompletion K) (q₂.adicCompletion L₂) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q₂ hq₂
  have hfin₁ : Module.finrank (Q.adicCompletion K) (q₁.adicCompletion L₁) = ℓ := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q₁ hq₁]
    exact hdeg₁
  have hfin₂ : Module.finrank (Q.adicCompletion K) (q₂.adicCompletion L₂) = ℓ := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q₂ hq₂]
    exact hdeg₂
  obtain ⟨M₁, ⟨e₁⟩, hfdM₁, hnormM₁, hfinM₁, hng₁⟩ :=
    exists_maxAbelianSubext_level (B := q₁.adicCompletion L₁) Q ℓ hℓ hfin₁
  obtain ⟨M₂, ⟨e₂⟩, hfdM₂, hnormM₂, hfinM₂, hng₂⟩ :=
    exists_maxAbelianSubext_level (B := q₂.adicCompletion L₂) Q ℓ hℓ hfin₂
  haveI := hfdM₁
  haveI := hnormM₁
  haveI := hfdM₂
  haveI := hnormM₂
  have hEq : M₁ = M₂ := by
    by_contra hne
    exact (NK.NUV2.TamePrimeLevel.normGroup_ne_of_finrank_eq_prime_tame Q ℓ hℓ hunram
        M₁ M₂ hfinM₁ hfinM₂ hne) (hng₁.symm.trans (hN.trans hng₂))
  exact ⟨e₁.trans ((IntermediateField.equivOfEq hEq).trans e₂.symm)⟩

end NK.Summary.NUV2.Tame
