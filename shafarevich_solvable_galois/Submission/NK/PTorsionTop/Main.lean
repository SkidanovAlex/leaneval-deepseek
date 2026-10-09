/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The corrected `δ`-detection: `p`-torsion of the topological abelianisation is `μ_p(κ)`

This is the point of the subproject.  For `κ = K_𝔭` the `𝔭`-adic completion of a number field
(`𝔭` a finite prime, `p` its residue characteristic) and `K'` a separable closure of `κ`,

  `Gal(K'/κ)` has `p`-torsion in its **topological** abelianisation
    ⟺  `κ` contains a primitive `p`-th root of unity,

i.e.

  `NK.PTorsionTop.HasPTorsionAbelianizationTop p (Gal(K'/κ)) ↔ zetaIndicator p κ = 1`.

The route is the one described in the module docstring of `Submission/Work/Mine/`

* the restriction to the maximal abelian subextension
  (`AlgEquiv.restrictNormalHom`) is surjective with kernel the **closure** of the commutator
  subgroup (`NK.LocalInputs.AbelianRank.fixingSubgroup_fixedField_eq_topologicalClosure`), so
  `Gal(K'/κ) ⧸ closure([G,G]) ≃* Gal(κ^{ab}/κ)` (`quotientTopologicalClosureCommEquivAbGal`);
* local reciprocity (`NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion`, from the datum
  `NK.LocalCFT.ArtinReciprocity κ K'`) gives `Gal(κ^{ab}/κ) ≃* κˣ^{∧}`;
* the `p`-torsion of `κˣ^{∧}` is `μ_p(κ)` (`NK.PTorsionTop.hasPTorsion_completionUnits_iff_zeta`).

**On the reciprocity datum.**  The statement below is proved from
`D : NK.LocalCFT.ArtinReciprocity κ K'` (equivalently `NK.LocalReciprocity.LubinTateInput`,
which is *defined* to be `Nonempty (ArtinReciprocity κ K')`).  Local class field theory for
`p`-adic fields is not a theorem of this workspace: it is the named input
`NK.LocalInputs.LocalGaloisInputsOfUnits.lubinTate` that every existing local bundle already
carries, so nothing is lost — but the formation "`p_torsion_iff`" is now a *theorem* about the
correct invariant, derived from that input, rather than an unexplained (and false) field about the
abstract abelianisation.  `hasPTorsionAbelianizationTop_iff_zeta_of_nonempty` states the same
result with the datum bundled as `Nonempty`.

## Main definitions and results

* `NK.PTorsionTop.quotientTopologicalClosureCommEquivAbGal`
* `NK.PTorsionTop.quotientTopologicalClosureCommEquiv` (the composite
  `Gal(K'/κ) ⧸ closure([G,G]) ≃* κˣ^{∧}`)
* `NK.PTorsionTop.abGalEquivCompletionUnits` (`Gal(κ^{ab}/κ) ≃* κˣ^{∧}`)
* `NK.PTorsionTop.hasPTorsionAbelianizationTop_iff_zeta`
-/
import Mathlib
import Submission.NK.PTorsionTop.UnitsTorsion
import Submission.NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
import Submission.NK.LocalInputs.AbelianRank.fixingSubgroup_fixedField_eq_topologicalClosure
import Submission.NK.LocalReciprocity.commutator_gal_maxAbelianSubext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.PTorsionTop

universe u v

noncomputable section

/-! ## The topological abelianisation of an absolute Galois group -/

/-- **The kernel of the restriction to the maximal abelian subextension is the closure of the
commutator subgroup**: this is the identification of `Gal(F^{ab}/F)` with the *topological*
abelianisation of `Gal(F'/F)`. -/
theorem ker_restrictNormalHom_maxAbelianSubext_eq {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := F')
        ↥(NK.LocalReciprocity.maxAbelianSubext F F')).ker =
      (commutator (F' ≃ₐ[F] F')).topologicalClosure := by
  haveI : IsGalois F ↥(NK.LocalReciprocity.maxAbelianSubext F F') :=
    NK.LocalReciprocity.instIsGaloisMaxAbelianSubext
  rw [IntermediateField.restrictNormalHom_ker, NK.LocalReciprocity.maxAbelianSubext]
  exact NK.LocalInputs.AbelianRank.fixingSubgroup_fixedField_eq_topologicalClosure
    (commutator (F' ≃ₐ[F] F'))

/-- **The topological abelianisation is the Galois group of the maximal abelian subextension**:
`Gal(F'/F) ⧸ closure([G_F,G_F]) ≃* Gal(F^{ab}/F)`. -/
noncomputable def quotientTopologicalClosureCommEquivAbGal {F : Type u} {F' : Type v}
    [Field F] [Field F'] [Algebra F F'] [IsGalois F F'] :
    (F' ≃ₐ[F] F') ⧸ (commutator (F' ≃ₐ[F] F')).topologicalClosure ≃*
      NK.LocalCFT.AbGal F F' := by
  haveI : IsGalois F ↥(NK.LocalReciprocity.maxAbelianSubext F F') :=
    NK.LocalReciprocity.instIsGaloisMaxAbelianSubext
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (ker_restrictNormalHom_maxAbelianSubext_eq (F := F) (F' := F')).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (AlgEquiv.restrictNormalHom_surjective (F := F)
          (K₁ := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) F'))

/-- **The reciprocity isomorphism `Gal(F^{ab}/F) ≃* Fˣ^{∧}`**, from the Artin reciprocity datum. -/
def abGalEquivCompletionUnits {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F') :
    NK.LocalCFT.AbGal F F' ≃* NK.LocalReciprocity.completionUnits F :=
  (Classical.choice (NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion D)).symm

/-- The composite `Gal(F'/F) ⧸ closure([G_F,G_F]) ≃* Fˣ^{∧}`: the topological abelianisation of
the absolute Galois group, identified with the profinite completion of the unit group (given the
reciprocity datum). -/
noncomputable def quotientTopologicalClosureCommEquiv {F : Type u} {F' : Type v} [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F') :
    (F' ≃ₐ[F] F') ⧸ (commutator (F' ≃ₐ[F] F')).topologicalClosure ≃*
      NK.LocalReciprocity.completionUnits F :=
  (quotientTopologicalClosureCommEquivAbGal (F := F) (F' := F')).trans
    (abGalEquivCompletionUnits D)

/-! ## The `δ`-detection -/

/-- **The `p`-torsion of the topological abelianisation of `Gal(K'/κ)` is `μ_p(κ)`.**

Given the local reciprocity datum `D` for `κ = K_𝔭` and its separable closure `K'`, the
topological abelianisation of `Gal(K'/κ)` has non-trivial `p`-torsion exactly when `κ` contains a
primitive `p`-th root of unity.  This is the corrected form of the `p_torsion_iff` field of
`NK.LocalAnabelian.PadicGaloisInputs` and friends. -/
theorem hasPTorsionAbelianizationTop_iff_zeta {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (D : NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K') :
    (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
      HasPTorsionAbelianizationTop p (Gal(K'/𝔭.adicCompletion K)) := by
  haveI : IsGalois (𝔭.adicCompletion K) K' := IsSepClosure.isGalois
  -- the topological abelianisation is `Gal(κ^{ab}/κ)`
  have hGal : HasPTorsionAbelianizationTop p (Gal(K'/𝔭.adicCompletion K)) ↔
      HasPTorsion p (NK.LocalCFT.AbGal (𝔭.adicCompletion K) K') := by
    change HasPTorsion p
      ((K' ≃ₐ[𝔭.adicCompletion K] K') ⧸
        (commutator (K' ≃ₐ[𝔭.adicCompletion K] K')).topologicalClosure) ↔ _
    exact hasPTorsion_congr_iff
      (quotientTopologicalClosureCommEquivAbGal (F := 𝔭.adicCompletion K) (F' := K')) p
  -- reciprocity identifies `Gal(κ^{ab}/κ)` with `κˣ^{∧}`
  have hAb : HasPTorsion p (NK.LocalCFT.AbGal (𝔭.adicCompletion K) K') ↔
      HasPTorsion p (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)) :=
    hasPTorsion_congr_iff (abGalEquivCompletionUnits (F := 𝔭.adicCompletion K) (F' := K') D) p
  exact ((hasPTorsion_completionUnits_iff_zeta 𝔭 hp hchar).symm.trans hAb.symm).trans hGal.symm

/-- **The `δ`-detection with the reciprocity datum bundled as `Nonempty`** (the form in which the
corrected input bundles carry it). -/
theorem hasPTorsionAbelianizationTop_iff_zeta_of_nonempty {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (hD : Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K')) :
    (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
      HasPTorsionAbelianizationTop p (Gal(K'/𝔭.adicCompletion K)) :=
  hasPTorsionAbelianizationTop_iff_zeta 𝔭 hp hchar K' (Classical.choice hD)

/-- **The `p`-torsion of `κˣ^{∧}` inside the Galois-theoretic picture**: the composite
`Gal(K'/κ) ⧸ closure([G,G]) ≃* κˣ^{∧}` of the topological abelianisation with reciprocity carries
`p`-torsion to `p`-torsion. -/
theorem hasPTorsion_topologicalAbelianization_iff_completionUnits {K : Type*} [Field K]
    [NumberField K] (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (D : NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K') :
    HasPTorsion p
        ((K' ≃ₐ[𝔭.adicCompletion K] K') ⧸
          (commutator (K' ≃ₐ[𝔭.adicCompletion K] K')).topologicalClosure) ↔
      HasPTorsion p (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)) :=
  hasPTorsion_congr_iff (quotientTopologicalClosureCommEquiv
    (F := 𝔭.adicCompletion K) (F' := K') D) p

end

end NK.PTorsionTop
