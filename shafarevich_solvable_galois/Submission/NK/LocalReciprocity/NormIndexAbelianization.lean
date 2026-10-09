import Mathlib
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
import Submission.NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization
import Submission.Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units
import Submission.Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_finrank_of_abelian_local
import Submission.Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_of_ringEquiv
import Submission.NK.GlobalCFTdeep.HasseIndex.LocalFieldTransport
import Submission.NK.LocalAnabelian.Basic
import Submission.NeukirchUchida.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm index of a finite Galois extension of a local field is the order of the
abelianised Galois group

For `K` a number field, `Q` a finite place of `K`, `B` a finite extension of the local field
`K_Q = Q.adicCompletion K` and `E / B` a finite Galois extension, the norm index

  `[Bˣ : N_{E/B} Eˣ]`

equals the order of the abelianisation of the Galois group `Gal(E/B)`.

This is the norm index theorem for a finite Galois extension of a local field; it is the
combination of

* the *norm index theorem* `[Kˣ : N Lˣ] = [L : K]` for a finite **abelian** extension, the standard
  form of local class field theory, and
* the *norm limitation theorem*, which identifies the norm group of `E/B` with the norm group of
  its maximal abelian subextension.

Both are consequences of Tate's theorem for local fields; here they are obtained by combining

* the local fundamental class `#H²(Gal(E/B), Eˣ) = [E : B]`
  (`NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank`),
* the cyclicity of `H²(Gal(E/B), Eˣ)`
  (`NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local`),
* Hilbert 90 for the units at every subgroup
  (`Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units`),
* Tate's theorem (`NK.NUV2.ArtinBridge.natCard_tateCohomology_eq_of_fundamental_class'`),
* the identification `Ĥ⁰(Gal(E/B), Eˣ) ≃ Bˣ ⧸ N Eˣ`
  (`Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units`) and
  `Ĥ⁻²(G, ℤ) ≃ Gᵃᵇ`
  (`Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization`).

The main statement `NK.LocalReciprocity.NormIndexAbelianization` is the same statement for
`B` and `E` in arbitrary universes; it is reduced to the universe-zero statement
`normIndexAbelianization_typeZero` by transporting along the `Shrink` (universe-zero) models
of a number field, exactly as in the global case
(`NK.NUV2.ArtinBridge.index_eq_card_abelianization_universe_bridge`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open IsDedekindDomain

universe u v w

namespace NK.LocalReciprocity

/-! ## Smallness of the universe-zero models -/

section Small

instance small_filter {α : Type u} [Small.{0} α] : Small.{0} (Filter α) :=
  small_of_injective (f := Filter.sets) (fun F G h => by
    apply Filter.ext
    intro s
    change s ∈ F.sets ↔ s ∈ G.sets
    rw [h])

instance small_cauchyFilter {α : Type u} [UniformSpace α] [Small.{0} α] :
    Small.{0} (CauchyFilter α) :=
  small_subtype (α := Filter α) (fun F => Cauchy F)

instance small_completion {α : Type u} [UniformSpace α] [Small.{0} α] :
    Small.{0} (UniformSpace.Completion α) :=
  small_quotient (inseparableSetoid (CauchyFilter α))

instance small_withVal {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [Small.{0} R] : Small.{0} (WithVal v) :=
  small_of_injective (WithVal.equiv v).injective

instance small_valuation_completion {R : Type u} {Γ₀ : Type v} [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) [Small.{0} R] :
    Small.{0} (v.Completion) := inferInstance

instance small_numberField {K : Type u} [Field K] [NumberField K] : Small.{0} K := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  exact Countable.toSmall K

instance small_adicCompletion {K : Type u} [Field K] [NumberField K]
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers K)) : Small.{0} (Q.adicCompletion K) :=
  small_of_injective (HeightOneSpectrum.adicCompletion.equiv K Q).injective

/-- A finite-dimensional extension of a small field is small. -/
theorem small_of_finiteDimensional {F B : Type*} [Field F] [Field B] [Algebra F B]
    [FiniteDimensional F B] [Small.{0} F] : Small.{0} B :=
  small_of_injective (Module.finBasis F B).equivFun.injective

end Small

/-! ## Transport of the abelianisation along a compatible pair of ring isomorphisms -/

/-- **The `MapsBase` computation for a compatible pair of ring equivalences**: the ring equivalence
of the total algebra maps the image of the base onto the image of the base. -/
theorem mapsBase_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE.toRingHom (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    Submission.NeukirchUchida.MapsBase (algebraMap B₀ E₀) (algebraMap B E) eE := by
  rw [Submission.NeukirchUchida.MapsBase]
  ext x
  simp only [Subring.mem_map, RingHom.mem_range]
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, hxy⟩
    exact ⟨eB a, (h a).symm.trans hxy⟩
  · rintro ⟨r, hr⟩
    refine ⟨algebraMap B E (eB.symm r), ⟨eB.symm r, rfl⟩, ?_⟩
    rw [h (eB.symm r), RingEquiv.apply_symm_apply eB r]
    exact hr

/-- **The abelianisations of a compatible pair of extensions have the same cardinality.** -/
theorem natCard_abelianization_eq_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E]
    [Field B₀] [Field E₀] [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    Nat.card (Abelianization (E ≃ₐ[B] E)) = Nat.card (Abelianization (E₀ ≃ₐ[B₀] E₀)) :=
  Nat.card_congr (NK.LocalAnabelian.abelianizationMulEquiv
    (Submission.NeukirchUchida.conjHomEquiv (mapsBase_of_ringEquiv eB eE h))).toEquiv.symm

/-! ## The norm index theorem at universe zero -/

/-- **The norm index theorem at universe zero.** -/
theorem normIndexAbelianization_typeZero
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E] :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (Abelianization (E ≃ₐ[B] E)) := by
  haveI hfdE : FiniteDimensional (Q.adicCompletion K) E :=
    Module.Finite.trans (R := Q.adicCompletion K) B E
  -- Hilbert 90 for every subgroup
  have h1 : ∀ H : Subgroup (E ≃ₐ[B] E),
      Subsingleton (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 1) :=
    fun H =>
      Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units H
  -- the local fundamental class at every subgroup
  have h2 : ∀ H : Subgroup (E ≃ₐ[B] E),
      Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) =
        Nat.card H := by
    intro H
    rw [Commons.NumberTheory.NumberField.Completion.NatCardP9.natCard_groupCohomology_two_res_units H]
    let C : IntermediateField B E := IntermediateField.fixedField H
    letI instAlgC : Algebra (Q.adicCompletion K) ↥C :=
      ((algebraMap B ↥C).comp (algebraMap (Q.adicCompletion K) B)).toAlgebra
    haveI instSTBC : IsScalarTower (Q.adicCompletion K) B ↥C :=
      IsScalarTower.of_algebraMap_eq (fun x => rfl)
    letI instModC : Module (Q.adicCompletion K) ↥C := instAlgC.toModule
    haveI instFdC : Module.Finite (Q.adicCompletion K) ↥C :=
      Module.Finite.trans (R := Q.adicCompletion K) B ↥C
    haveI instFdC' : FiniteDimensional (Q.adicCompletion K) ↥C := instFdC
    haveI instSTCE : IsScalarTower (Q.adicCompletion K) ↥C E :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        rw [IsScalarTower.algebraMap_apply (Q.adicCompletion K) B ↥C x,
          ← IsScalarTower.algebraMap_apply B ↥C E (algebraMap (Q.adicCompletion K) B x),
          ← IsScalarTower.algebraMap_apply (Q.adicCompletion K) B E x])
    rw [NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank (K := K) Q
          (F := ↥C) (E := E),
      IntermediateField.finrank_fixedField_eq_card H]
  obtain ⟨α, hα⟩ :=
    NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local (K := K) Q
      (F := B) (E := E)
  have hα' : addOrderOf α = Nat.card (E ≃ₐ[B] E) := by
    rw [hα, ← IsGalois.card_aut_eq_finrank B E]
  have htate := NK.NUV2.ArtinBridge.natCard_tateCohomology_eq_of_fundamental_class'
    (Rep.ofAlgebraAutOnUnits B E) h1 h2 α hα'
  have hzero := Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units B E
  obtain ⟨e⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization
      (E ≃ₐ[B] E)
  calc Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B)))
      = Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits B E) 0) := hzero.symm
    _ = Nat.card (tateCohomology (Rep.trivial ℤ (E ≃ₐ[B] E) ℤ) (-2)) := htate.symm
    _ = Nat.card (Abelianization (E ≃ₐ[B] E)) :=
        (Nat.card_congr e.toEquiv).trans (Nat.card_congr Additive.toMul)

/-! ## The universe bridge -/

/-- **The universe bridge**: the norm index theorem for `B`, `E` in arbitrary universes follows
from the universe-zero statement, by transporting along the `Shrink` models. -/
theorem normIndexAbelianization_universeBridge
    (h0 : ∀ {K : Type} [Field K] [NumberField K]
        (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        {B E : Type} [Field B] [Field E]
        [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
        [IsScalarTower (Q.adicCompletion K) B E]
        [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E] [IsGalois B E],
        Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
          Nat.card (Abelianization (E ≃ₐ[B] E)))
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type*} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E] :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (Abelianization (E ≃ₐ[B] E)) := by
  -- smallness of the models
  haveI hKsmall : Small.{0} K := inferInstance
  haveI hBsmall : Small.{0} B := small_of_finiteDimensional (F := Q.adicCompletion K) (B := B)
  haveI hfdEK : FiniteDimensional (Q.adicCompletion K) E :=
    Module.Finite.trans (R := Q.adicCompletion K) B E
  haveI hEsmall : Small.{0} E := small_of_finiteDimensional (F := Q.adicCompletion K) (B := E)
  -- the universe-zero number field and its place
  let K₀ : Type := Shrink.{0} K
  haveI : NumberField K₀ := NK.GlobalCFTdeep.HasseIndex.shrink_numberField K
  let Q₀ : HeightOneSpectrum (NumberField.RingOfIntegers K₀) :=
    NK.GlobalCFTdeep.Transport.finitePlaceEquiv (Shrink.ringEquiv K).symm Q
  let eU : Q.adicCompletion K ≃+* Q₀.adicCompletion K₀ :=
    NK.GlobalCFTdeep.HasseIndex.finiteLocalEquiv (Shrink.ringEquiv K).symm Q
  -- the universe-zero models of `B` and `E`
  let B₀ : Type := Shrink.{0} B
  let E₀ : Type := Shrink.{0} E
  let eB : B ≃+* B₀ := (Shrink.ringEquiv B).symm
  let eE : E ≃+* E₀ := (Shrink.ringEquiv E).symm
  letI : Algebra (Q₀.adicCompletion K₀) B₀ :=
    RingHom.toAlgebra
      (eB.toRingHom.comp ((algebraMap (Q.adicCompletion K) B).comp eU.symm.toRingHom))
  letI : Algebra (Q₀.adicCompletion K₀) E₀ :=
    RingHom.toAlgebra
      (eE.toRingHom.comp ((algebraMap (Q.adicCompletion K) E).comp eU.symm.toRingHom))
  letI : Algebra B₀ E₀ :=
    RingHom.toAlgebra (eE.toRingHom.comp ((algebraMap B E).comp eB.symm.toRingHom))
  -- the scalar-tower relation
  have hst : IsScalarTower (Q₀.adicCompletion K₀) B₀ E₀ :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      show eE (algebraMap (Q.adicCompletion K) E (eU.symm x)) =
        eE (algebraMap B E (eB.symm
          (eB (algebraMap (Q.adicCompletion K) B (eU.symm x)))))
      rw [RingEquiv.symm_apply_apply,
        ← IsScalarTower.algebraMap_apply (Q.adicCompletion K) B E (eU.symm x)])
  haveI : IsScalarTower (Q₀.adicCompletion K₀) B₀ E₀ := hst
  -- finiteness and Galois-ness of the transported extension
  have hcB : (algebraMap (Q₀.adicCompletion K₀) B₀).comp
        (eU : Q.adicCompletion K →+* Q₀.adicCompletion K₀) =
      (eB : B →+* B₀).comp (algebraMap (Q.adicCompletion K) B) := by
    refine RingHom.ext fun x => ?_
    show eB (algebraMap (Q.adicCompletion K) B (eU.symm (eU x))) =
      eB (algebraMap (Q.adicCompletion K) B x)
    rw [RingEquiv.symm_apply_apply]
  have hcE : (algebraMap (Q₀.adicCompletion K₀) E₀).comp
        (eU : Q.adicCompletion K →+* Q₀.adicCompletion K₀) =
      (eE : E →+* E₀).comp (algebraMap (Q.adicCompletion K) E) := by
    refine RingHom.ext fun x => ?_
    show eE (algebraMap (Q.adicCompletion K) E (eU.symm (eU x))) =
      eE (algebraMap (Q.adicCompletion K) E x)
    rw [RingEquiv.symm_apply_apply]
  have hcBE : (algebraMap B₀ E₀).comp (eB : B →+* B₀) =
      (eE : E →+* E₀).comp (algebraMap B E) := by
    refine RingHom.ext fun x => ?_
    show eE (algebraMap B E (eB.symm (eB x))) = eE (algebraMap B E x)
    rw [RingEquiv.symm_apply_apply]
  haveI hfdB₀ : FiniteDimensional (Q₀.adicCompletion K₀) B₀ :=
    Module.Finite.of_equiv_equiv eU eB hcB
  haveI hfdBE₀ : FiniteDimensional B₀ E₀ :=
    Module.Finite.of_equiv_equiv eB eE hcBE
  haveI hgal₀ : IsGalois B₀ E₀ :=
    IsGalois.of_equiv_equiv (f := eB) (g := eE) hcBE
  -- the universe-zero statement at the models
  have hmodel := h0 (K := K₀) (Q := Q₀) (B := B₀) (E := E₀)
  -- transport the two sides back
  have hcompat : ∀ x : B, eE.toRingHom (algebraMap B E x) = algebraMap B₀ E₀ (eB x) :=
    fun x => (congrArg (fun y : B => eE.toRingHom (algebraMap B E y))
      (RingEquiv.symm_apply_apply eB x)).symm
  have hnorm := Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_of_ringEquiv
    eB eE hcompat
  have hab := natCard_abelianization_eq_of_ringEquiv eB eE hcompat
  calc Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B)))
      = Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))) := hnorm
    _ = Nat.card (Abelianization (E₀ ≃ₐ[B₀] E₀)) := hmodel
    _ = Nat.card (Abelianization (E ≃ₐ[B] E)) := hab.symm

/-! ## The main statement -/

theorem NormIndexAbelianization
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type*} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E] :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (Abelianization (E ≃ₐ[B] E)) :=
  normIndexAbelianization_universeBridge normIndexAbelianization_typeZero Q

end NK.LocalReciprocity
