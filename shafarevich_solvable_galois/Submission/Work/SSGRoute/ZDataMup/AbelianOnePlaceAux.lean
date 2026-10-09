import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.LocalCFT.NormGroup.normGroup_sup_eq_inf
import Submission.NK.LocalCFT.NormGroup.normGroup_le_iff
import Submission.NK.LocalCFT.NormGroup.normGroup_eq_iff
import Submission.NK.LocalCFT.Basic
import Submission.NK.NUV2.Final.Assembly
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.LocalReciprocity.MaxAbelianSetup
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
import Submission.NeukirchUchida.Local.PlaceUnder
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField
open NumberField IsDedekindDomain


namespace Work.SSGRoute.ZDataMup

/-- The sup of a family of fixing subgroups is the fixing subgroup of the infimum. -/
theorem fixingSubgroup_iSup_eq_iInf {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] {ι : Type*}
    (A : ι → IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')) :
    (⨆ i, A i).fixingSubgroup = ⨅ i, (A i).fixingSubgroup := by
  refine le_antisymm (le_iInf fun j => IntermediateField.fixingSubgroup_le (le_iSup A j)) ?_
  have h : ∀ i, A i ≤ IntermediateField.fixedField (⨅ i, (A i).fixingSubgroup) := by
    intro i
    rw [IntermediateField.le_iff_le]
    exact iInf_le _ i
  have h2 : (⨆ i, A i) ≤ IntermediateField.fixedField (⨅ i, (A i).fixingSubgroup) := iSup_le h
  rwa [IntermediateField.le_iff_le] at h2

/-- **"Norm group of a join" for a family of levels of `F^{ab}`**: the norm group of the join of a
family of levels is the intersection of the norm groups. -/
theorem normGroup_iSup_eq_iInf {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F')
    {ι : Type*} (A : ι → IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    (hfd : ∀ i, FiniteDimensional F (A i)) (hn : ∀ i, Normal F (A i))
    [FiniteDimensional F ↥(⨆ i, A i)] [Normal F ↥(⨆ i, A i)] :
    NK.LocalReciprocity.normGroup F ↥(⨆ i, A i) = ⨅ i, NK.LocalReciprocity.normGroup F ↥(A i) := by
  have key : ∀ i, NK.LocalReciprocity.normGroup F ↥(A i) =
      (A i).fixingSubgroup.comap D.artin := by
    intro i
    haveI := hfd i
    haveI := hn i
    exact NK.LocalCFT.NormGroup.normGroup_eq_iff_comap_fixingSubgroup D (A i)
  rw [NK.LocalCFT.NormGroup.normGroup_eq_iff_comap_fixingSubgroup D (⨆ i, A i),
    (@fixingSubgroup_iSup_eq_iInf F F' _ _ _ _ ι A), Subgroup.comap_iInf]
  exact iInf_congr fun i => (key i).symm

/-- **Realization of a finite abelian extension as a level of the maximal abelian subextension.**
An extension `E` of a field `B` which is finite, Galois and separable embeds into the separable
closure of `B`; when `Gal(E/B)` is commutative its image lies in the maximal abelian subextension,
and is an intermediate field there. -/
theorem exists_level_realization {B : Type*} [Field B] {E : Type*} [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] [Algebra.IsSeparable B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    ∃ (Λ : IntermediateField B (NK.LocalReciprocity.maxAbelianSubext B (SeparableClosure B))),
      Nonempty (E ≃ₐ[B] ↥Λ) := by
  classical
  let ψ : E →ₐ[B] (SeparableClosure B) := IsSepClosed.lift
  have hmem : ∀ x : E, ψ x ∈ ψ.fieldRange := fun x => ⟨x, rfl⟩
  let e : E ≃ₐ[B] ↥(ψ.fieldRange) :=
    AlgEquiv.ofBijective (ψ.codRestrict ψ.fieldRange.toSubalgebra hmem)
      ⟨fun a b h => ψ.injective (Subtype.ext_iff.mp h), fun y => by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨x, Subtype.ext hx⟩⟩
  haveI : FiniteDimensional B ↥(ψ.fieldRange) := e.toLinearEquiv.finiteDimensional
  haveI : IsGalois B ↥(ψ.fieldRange) := IsGalois.of_algEquiv e
  have hcomm' : ∀ a b : ↥(ψ.fieldRange) ≃ₐ[B] ↥(ψ.fieldRange), a * b = b * a := by
    intro a b
    exact ((AlgEquiv.autCongr e).symm).injective (by
      rw [map_mul, map_mul]
      exact hcomm _ _)
  have hle : ψ.fieldRange ≤ NK.LocalReciprocity.maxAbelianSubext B (SeparableClosure B) :=
    NK.LocalReciprocity.le_maxAbelianSubext_of_commutative _ hcomm'
  exact ⟨IntermediateField.restrict hle, ⟨e.trans (IntermediateField.restrictAlgEquiv hle)⟩⟩

/-- **The local norm subgroup at a finite place is the norm group of the completion.** -/
theorem localNormSubgroup_ofFinite_eq_normGroup {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite Q) =
      @NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L) _
        _ (Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq) := by
  rw [← NK.CFTLib.IdeleHasse.range_localNormFinite_eq_localNormSubgroup Q q hq]
  rfl

section Completeness

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **The `B`-algebra map from the completion of an intermediate field into the completion of the
top field.** -/
noncomputable def adjCompletionHom (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (M : IntermediateField K L) :
    @AlgHom (Q.adicCompletion K)
      ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion M)
      (q.adicCompletion L) _ _ _
      (Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
        (Submission.NeukirchUchida.Local.placeUnder M q)
        (Submission.NeukirchUchida.Local.liesOver_placeUnder M q Q))
      (Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq) := by
  letI : Algebra (Q.adicCompletion K)
      ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
      (Submission.NeukirchUchida.Local.placeUnder M q)
      (Submission.NeukirchUchida.Local.liesOver_placeUnder M q Q)
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  refine
    { toFun := Commons.RingTheory.Henselian.adicCompletionMap
        (Submission.NeukirchUchida.Local.placeUnder M q) q
        (Ideal.LiesOver.mk (by rw [Submission.NeukirchUchida.Local.placeUnder_asIdeal]))
      map_one' := map_one _
      map_mul' := map_mul _
      map_zero' := map_zero _
      map_add' := map_add _
      commutes' := ?_ }
  intro b
  show Commons.RingTheory.Henselian.adicCompletionMap (Submission.NeukirchUchida.Local.placeUnder M q) q
      (Ideal.LiesOver.mk (by rw [Submission.NeukirchUchida.Local.placeUnder_asIdeal]))
      (Commons.RingTheory.Henselian.adicCompletionMap Q (Submission.NeukirchUchida.Local.placeUnder M q)
        (Submission.NeukirchUchida.Local.liesOver_placeUnder M q Q) b) =
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq b
  have h := Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp (K := K) (L := ↥M)
    (M := L) Q (Submission.NeukirchUchida.Local.placeUnder M q) q
    (Submission.NeukirchUchida.Local.liesOver_placeUnder M q Q)
    (Ideal.LiesOver.mk (by rw [Submission.NeukirchUchida.Local.placeUnder_asIdeal])) hq
  exact DFunLike.congr_fun h b

/-- **The image of the completion of an intermediate field in the completion of the top field**, as
an intermediate field over `K_Q`. -/
noncomputable def localFieldImage (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) (M : IntermediateField K L) :
    @IntermediateField (Q.adicCompletion K) (q.adicCompletion L) _ _
      (Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq) := by
  letI : Algebra (Q.adicCompletion K)
      ((Submission.NeukirchUchida.Local.placeUnder M q).adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q
      (Submission.NeukirchUchida.Local.placeUnder M q)
      (Submission.NeukirchUchida.Local.liesOver_placeUnder M q Q)
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  exact IntermediateField.map (adjCompletionHom Q q hq M) ⊤

end Completeness

end Work.SSGRoute.ZDataMup
