import Mathlib
import Submission.Work.SSGRoute.local_lifting_setup
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Sizes of the residue field of the pullback of a place of `ℚ̄` to `ℚ`

The main theorem `Work.SSGRoute.finite_card_residueField_comap_bot` computes the residue field of
the place of `ℚ̄` below a finite place `A`, pulled back to the bottom intermediate field
`⊥ : IntermediateField ℚ ↥L` (a copy of `ℚ` inside `L`): it is finite and has `residueChar A`
elements.  This is the size statement needed in the tame lifting argument (the residue field of
`A ∩ ℚ` is `𝔽_p` with `p = residueChar A`).

The proof is a comparison of residue fields, split into two general lemmas:

* `residueField_comap_bot_ringEquiv` — pulling a valuation subring back along the bottom
  intermediate field `⊥ : IntermediateField F E` (a copy of `F`) does not change its residue
  field, since the canonical map `F → ↥⊥` is an isomorphism;
* `residueField_valuationSubringAtPrime_ringEquiv` — the residue field of the localisation of a
  Dedekind domain at a height one prime `𝔭` is the residue field `R ⧸ 𝔭`.

The finiteness of `𝓞 ℚ ⧸ 𝔭` is `Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum`.
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-- **The residue field of the pullback of a valuation subring to the bottom intermediate field.**

For a field extension `F ⊆ E` and a valuation subring `V` of `E`, the valuation subrings
`V.comap (algebraMap ↥⊥ E)` (of `↥⊥`, the copy of `F` inside `E`) and `V.comap (algebraMap F E)`
(of `F`) correspond to each other under the canonical isomorphism `F ≃+* ↥⊥`, so their residue
fields are isomorphic. -/
theorem residueField_comap_bot_ringEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E] (V : ValuationSubring E) :
    Nonempty (IsLocalRing.ResidueField
        ↥(V.comap (algebraMap ↥(⊥ : IntermediateField F E) E)) ≃+*
      IsLocalRing.ResidueField ↥(V.comap (algebraMap F E))) := by
  set W : ValuationSubring ↥(⊥ : IntermediateField F E) :=
    V.comap (algebraMap ↥(⊥ : IntermediateField F E) E) with hW
  let e : F ≃+* ↥(⊥ : IntermediateField F E) := (IntermediateField.botEquiv F E).symm.toRingEquiv
  have he : (e : F →+* ↥(⊥ : IntermediateField F E))
      = algebraMap F ↥(⊥ : IntermediateField F E) := by
    ext x
    simpa [e] using IntermediateField.botEquiv_symm (F := F) (E := E) x
  have hcomap : W.comap (e : F →+* ↥(⊥ : IntermediateField F E)) = V.comap (algebraMap F E) := by
    rw [he, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq F ↥(⊥ : IntermediateField F E) E]
  let φ : ↥(W.comap (e : F →+* ↥(⊥ : IntermediateField F E))) →+* ↥W :=
    { toFun := fun x => ⟨e x, ValuationSubring.mem_comap.mp x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h' : e (x : F) = e (y : F) := by
        simpa [φ] using congrArg (fun z : ↥W => (z : ↥(⊥ : IntermediateField F E))) hxy
      exact Subtype.ext (e.injective h')
    · intro y
      obtain ⟨x, hx⟩ := e.surjective (y : ↥(⊥ : IntermediateField F E))
      refine ⟨⟨x, ?_⟩, ?_⟩
      · show e x ∈ W
        rw [hx]; exact y.2
      · ext
        simp [φ, hx]
  refine ⟨?_⟩
  rw [← hcomap]
  exact (IsLocalRing.ResidueField.mapEquiv (RingEquiv.ofBijective φ hφ)).symm

/-- **The residue field of a Dedekind localisation at a height one prime.**

For a Dedekind domain `R` with fraction field `K` and a height one prime `𝔭`, the residue field of
the localisation `R_𝔭 = valuationSubringAtPrime K 𝔭` is the residue field `R ⧸ 𝔭` of `𝔭`. -/
theorem residueField_valuationSubringAtPrime_ringEquiv
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    Nonempty (IsLocalRing.ResidueField
        ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) ≃+*
      R ⧸ v.asIdeal) := by
  haveI := v.isMaximal
  let e := IsLocalization.algEquiv v.asIdeal.primeCompl
      ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
      (Localization.AtPrime v.asIdeal)
  refine ⟨(IsLocalRing.ResidueField.mapEquiv e.toRingEquiv).trans ?_⟩
  exact (RingEquiv.ofBijective
    (algebraMap (R ⧸ v.asIdeal) (Ideal.ResidueField v.asIdeal))
    (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal)).symm

theorem finite_card_residueField_comap_bot
    (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] :
    Finite (IsLocalRing.ResidueField
      ↥((A.1.comap (algebraMap ↥L SSGRoute.QBar)).comap
        (algebraMap ↥(⊥ : IntermediateField ℚ ↥L) ↥L))) ∧
    Nat.card (IsLocalRing.ResidueField
      ↥((A.1.comap (algebraMap ↥L SSGRoute.QBar)).comap
        (algebraMap ↥(⊥ : IntermediateField ℚ ↥L) ↥L))) = Work.SSGRoute.residueChar A := by
  classical
  obtain ⟨e1⟩ := residueField_comap_bot_ringEquiv (F := ℚ) (E := ↥L)
    (V := A.1.comap (algebraMap ↥L SSGRoute.QBar))
  have hcomap : (A.1.comap (algebraMap ↥L SSGRoute.QBar)).comap (algebraMap ℚ ↥L)
      = A.1.comap (algebraMap ℚ SSGRoute.QBar) := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq ℚ ↥L SSGRoute.QBar]
  have hprime : A.1.comap (algebraMap ℚ SSGRoute.QBar)
      = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ
          (Submission.NeukirchUchida.primeOf A.1 A.2) :=
    Submission.NeukirchUchida.primeOf_spec A.1 A.2
  obtain ⟨e2⟩ := residueField_valuationSubringAtPrime_ringEquiv (K := ℚ)
    (Submission.NeukirchUchida.primeOf A.1 A.2)
  have e : IsLocalRing.ResidueField
        ↥((A.1.comap (algebraMap ↥L SSGRoute.QBar)).comap
          (algebraMap ↥(⊥ : IntermediateField ℚ ↥L) ↥L))
      ≃+* (NumberField.RingOfIntegers ℚ ⧸
        (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) :=
    ((hcomap.trans hprime) ▸ e1).trans e2
  refine ⟨?_, ?_⟩
  · haveI : Finite (NumberField.RingOfIntegers ℚ ⧸
        (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum _
    exact Finite.of_equiv (NumberField.RingOfIntegers ℚ ⧸
        (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) e.symm
  · rw [Nat.card_congr e.toEquiv]
    rfl

end Work.SSGRoute
