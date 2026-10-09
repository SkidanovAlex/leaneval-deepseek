import Mathlib
import Submission.Work.SSGRoute.E1aClean.decompDatum
import Submission.Work.SSGRoute.E1aClean.decompField_embeds_completion
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
import Submission.Work.SSGRoute.E1aClean.extendScalars_finDimensional_of_ker
import Submission.Work.SSGRoute.E1aClean.extendScalars_isGalois_of_normal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean

open scoped Pointwise

/-- **The structural facts of the decomposition-field datum** `(k^h, Ω, K^h)` of a place `A` of
`Ω`, where `k^h = Ω^{D_A}` (`D_A = decomp k A`) and `K^h = Ω^{D_A ⊓ Gal(Ω/K)} = K·k^h`, viewed as
an extension of `k^h`:

1. `Ω` is an algebraic closure of `k^h` (`E1cGeneric` needs this at the local datum);
2. `D_A` is exactly the Galois group of `Ω` over `k^h` (closedness of `D_A`);
3. `K^h` is finite over `k^h` (the compositum with `K`, finite over `k`);
4. `K^h/k^h` is Galois (compositum of the Galois extension `K/k^h` with `k^h`).

Reviewer pointers: item 1 is `PT/Henselian/ConjugacyPlaces.lean:45` (`IsAlgClosure ↥(mup.decompField) Ω`
with `decompField = fixedField (decomp k A)`); item 2 is `PTembedding.fixingSubgroup_decompField`
(`PTembedding/mup_kummer_defs.lean:142`), using closedness of the decomposition group
(`Work.SSGRoute.isClosed_decomp_valuationSubring` in `inf_inertia_closure_eq_bot.lean`, or
`Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring`). -/
theorem decompField_datum_facts (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsGalois k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω) :
    IsAlgClosure ↥(IntermediateField.fixedField (SSGRoute.decomp k A)) Ω ∧
    (IntermediateField.fixedField (SSGRoute.decomp k A)).fixingSubgroup = SSGRoute.decomp k A ∧
    FiniteDimensional ↥(IntermediateField.fixedField (SSGRoute.decomp k A))
      ↥(IntermediateField.extendScalars
        (show IntermediateField.fixedField (SSGRoute.decomp k A) ≤
          IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)
        from IntermediateField.fixedField_le inf_le_left)) ∧
    IsGalois ↥(IntermediateField.fixedField (SSGRoute.decomp k A))
      ↥(IntermediateField.extendScalars
        (show IntermediateField.fixedField (SSGRoute.decomp k A) ≤
          IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)
        from IntermediateField.fixedField_le inf_le_left)) := by
  classical
  -- ## The decomposition group is closed, and it is the Galois group of `Ω` over `k^h`.
  have hDcl : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A
  have hfixkh : (IntermediateField.fixedField (SSGRoute.decomp k A)).fixingSubgroup =
      SSGRoute.decomp k A :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨SSGRoute.decomp k A, hDcl⟩ : ClosedSubgroup (Ω ≃ₐ[k] Ω))
  -- `Gal(Ω/K) = (res k K).ker`, and it is closed too, so `D_A ⊓ Gal(Ω/K)` is closed.
  have hkerres : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  have hGcl : IsClosed (((SSGRoute.res k K).ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    rw [hkerres]
    exact InfiniteGalois.fixingSubgroup_isClosed K
  have hfixKh :
      (IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)).fixingSubgroup =
        SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker, hDcl.inter hGcl⟩ :
        ClosedSubgroup (Ω ≃ₐ[k] Ω))
  -- ## The restriction homomorphism from the decomposition group to `Gal(K/k)`.
  let φ : ↥((IntermediateField.fixedField (SSGRoute.decomp k A)).fixingSubgroup) →* (K ≃ₐ[k] K) :=
    (SSGRoute.res k K).comp
      (IntermediateField.fixedField (SSGRoute.decomp k A)).fixingSubgroup.subtype
  have hkerφ : ((SSGRoute.res k K).comp
        (IntermediateField.fixedField (SSGRoute.decomp k A)).fixingSubgroup.subtype).ker =
      (IntermediateField.fixedField
        (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)).fixingSubgroup.subgroupOf
        (IntermediateField.fixedField (SSGRoute.decomp k A)).fixingSubgroup := by
    rw [← MonoidHom.comap_ker, Subgroup.comap_subtype, hfixKh, hfixkh,
      Subgroup.inf_subgroupOf_left]
  -- ## `Gal(K/k)` is finite.
  haveI hKf : Finite (K ≃ₐ[k] K) :=
    (Nat.card_pos_iff.mp (by
      rw [IsGalois.card_aut_eq_finrank (F := k) (E := ↥K)]
      exact Module.finrank_pos)).2
  -- ## `Gal(Ω/K^h)` is normal in `Gal(Ω/k^h)`.
  have hN : ((IntermediateField.fixedField
        (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)).fixingSubgroup.subgroupOf
        (IntermediateField.fixedField (SSGRoute.decomp k A)).fixingSubgroup).Normal := by
    rw [← hkerφ]
    exact MonoidHom.normal_ker φ
  -- ## `Ω` is algebraic over `k^h`.
  have hAlg : Algebra.IsAlgebraic ↥(IntermediateField.fixedField (SSGRoute.decomp k A)) Ω :=
    Algebra.IsAlgebraic.tower_top (K := k)
      (L := ↥(IntermediateField.fixedField (SSGRoute.decomp k A))) (A := Ω)
  refine ⟨⟨IsAlgClosure.isAlgClosed k, hAlg⟩, hfixkh, ?_, ?_⟩
  · exact extendScalars_finDimensional_of_ker (γ := K ≃ₐ[k] K)
      (h := IntermediateField.fixedField_le inf_le_left) φ hkerφ
  · exact extendScalars_isGalois_of_normal
      (h := IntermediateField.fixedField_le inf_le_left) hN

end Work.SSGRoute.E1aClean
