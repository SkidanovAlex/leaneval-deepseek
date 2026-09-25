import Submission.NK.Reconstruct.exists_sigma_of_localCorrespondence
import Submission.NK.EndgameRepair.LevelIsoInputGeneral
import Submission.NK.EndgameRepair.LevelPairData

/-!
# The σ-producing step of Neukirch–Uchida, on the **corrected** rank hypothesis

This is `NK.Reconstruct.exists_sigma_of_localCorrespondence` — the σ-producing step of the Shimizu
route to CoNF XII Thm 12.2.1 — with its three `rankGamma`-inputs
(referred to below as "the three rank inputs") replaced by the single hypothesis

`NK.Reconstruct.Fourf5InputGen K₁' ℓ`   (Shimizu's Proposition 4f.5),

which is the *only* way in which the original proof used them: all three entered through
`NK.Reconstruct.fourf5_gen_of_rankInputs`, inside the level-pair bridge.  The level-pair bridge on
the corrected hypothesis is `NK.EndgameRepair.levelIsoInput_of_localCorrespondence_fourf5`
(`Submission/Work/EndgameRepair/LevelIsoInputGeneral.lean`).

`Fourf5InputGen` is *satisfiable*: `NK.RankTheoryDeep.fourf5Gen_of_correctedResidualsDeep` derives
it from `NK.RankTheoryDeep.CorrectedResidualsDeep Ω ℓ`, whose fields are named classical theorems
(the local unit theorem, ℓ-adic Artin reciprocity, CoNF (10.3.7)/(10.3.20), and Shimizu's
kernel-rank input).  By contrast the old hypothesis is refuted: `NK.RankTheoryDeep` proves
`¬ NK.Reconstruct.HausRankInput Ω ℓ` for every prime `ℓ`
(`NK.RankTheoryDeep.not_hausRankInput`).

## Contents

* `NK.EndgameRepair.exists_sigma_of_localCorrespondence_corrected` — the existence half, with
  `Fourf5InputGen K₁' ℓ` as the rank hypothesis (ambient `ℚ`-algebra structure on `K₁'`);
* `NK.EndgameRepair.neukirch_uchida_of_localCorrespondence_corrected` — its `∃!` form, using the
  *proved* `Submission.NeukirchUchida.unique_sigma`;
* the same two with `NK.RankTheoryDeep.CorrectedResidualsDeep K₁' ℓ` (resp.
  `CorrectedResidualsDerived K₁ K₁' ℓ`) as the single rank hypothesis;
* the `_derived` forms, in which the `ℚ`-algebra structure on `K₁'` is derived from
  `[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']` by
  `NK.ReconstructEndgame.ratAlgebra`/`isSepClosure_rat_of_numberField`/`isGalois_rat_of_numberField`,
  exactly as in `Submission/Work/ReconstructEndgame/Main.lean`.

The proof of the main theorem is the on-disk proof verbatim; only steps 6 and 7 change, because the
level-pair bridge is now stated against `Fourf5InputGen`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.EndgameRepair

open NK.Reconstruct
open scoped NumberField Pointwise

attribute [local instance] NK.Reconstruct.NumFieldIn.finite
  NK.Reconstruct.NumFieldIn.numberField

section Main

theorem exists_sigma_of_localCorrespondence_corrected {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [Algebra ℚ K₁'] [IsGalois ℚ K₁']
    [IsSepClosure ℚ K₁'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : NK.Reconstruct.Fourf5InputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  -- ## Step 1: put both separable closures into the single field `K₁'`
  haveI hstA : IsScalarTower ℚ K₁ K₁' := isScalarTower_rat_of_numberField
  haveI hsepClosed : IsSepClosed K₁' := IsSepClosure.sep_closed ℚ
  haveI halg : Algebra.IsAlgebraic ℚ K₁' := inferInstance
  obtain ⟨ι, hι⟩ := NK.Reconstruct.exists_algebra_isSepClosure (K₂ := K₂) (K₁' := K₁') halg
  letI : Algebra K₂ K₁' := ι.toRingHom.toAlgebra
  haveI hιS : IsSepClosure K₂ K₁' := hι
  -- ## Step 2: the model `A` of `K₁` inside `K₁'`
  let fA : K₁ →ₐ[ℚ] K₁' := baseAlgHom K₁ K₁'
  let eA : K₁ ≃+* ↥fA.fieldRange :=
    (AlgEquiv.ofInjective fA (RingHom.injective (fA : K₁ →+* K₁'))).toRingEquiv
  have hA : ∀ x : K₁, (algebraMap ↥fA.fieldRange K₁') (eA x) = algebraMap K₁ K₁' x := fun x => rfl
  haveI hnfA : NumberField ↥fA.fieldRange := numberField_model fA.fieldRange eA hA
  haveI hfdA : FiniteDimensional ℚ ↥fA.fieldRange := by
    let fL : K₁ →ₗ[ℚ] ↥fA.fieldRange :=
      { toFun := fun x => ⟨fA x, ⟨x, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add fA x y)
        map_smul' := fun q x => Subtype.ext (map_smul fA q x) }
    exact Module.Finite.of_surjective fL
      (fun y => ⟨Classical.choose y.2, Subtype.ext (Classical.choose_spec y.2)⟩)
  haveI hspA : IsSepClosure ↥fA.fieldRange K₁' := isSepClosure_model fA.fieldRange eA hA
  let A : NumFieldIn ℚ K₁' := ⟨fA.fieldRange, hfdA, hnfA⟩
  -- ## Step 3: the model `B` of `K₂` inside `K₁'`
  let eB : K₂ ≃+* ↥ι.fieldRange :=
    (AlgEquiv.ofInjective ι (RingHom.injective (ι : K₂ →+* K₁'))).toRingEquiv
  have hB : ∀ x : K₂, (algebraMap ↥ι.fieldRange K₁') (eB x) = algebraMap K₂ K₁' x := fun x => rfl
  haveI hnfB : NumberField ↥ι.fieldRange := numberField_model ι.fieldRange eB hB
  haveI hfdB : FiniteDimensional ℚ ↥ι.fieldRange := by
    let fL : K₂ →ₗ[ℚ] ↥ι.fieldRange :=
      { toFun := fun x => ⟨ι x, ⟨x, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add ι x y)
        map_smul' := fun q x => Subtype.ext (map_smul ι q x) }
    exact Module.Finite.of_surjective fL
      (fun y => ⟨Classical.choose y.2, Subtype.ext (Classical.choose_spec y.2)⟩)
  haveI hspB : IsSepClosure ↥ι.fieldRange K₁' := isSepClosure_model ι.fieldRange eB hB
  let B : NumFieldIn ℚ K₁' := ⟨ι.fieldRange, hfdB, hnfB⟩
  -- ## Step 4: the conjugate `ψ` of `ϕ` by the isomorphism of separable closures
  let e : K₂' ≃ₐ[K₂] K₁' := IsSepClosure.equiv K₂ K₂' K₁'
  let ψ : Gal(K₁'/K₁) ≃* Gal(K₁'/K₂) :=
    { toFun := fun g => algEquivConjHom e (ϕ g)
      invFun := fun h => ϕ.symm (algEquivConjHom e.symm h)
      left_inv := by
        intro g
        show ϕ.symm (algEquivConjHom e.symm (algEquivConjHom e (ϕ g))) = g
        rw [algEquivConjHom_symm_apply_apply e (ϕ g), MulEquiv.symm_apply_apply]
      right_inv := by
        intro h
        show algEquivConjHom e (ϕ (ϕ.symm (algEquivConjHom e.symm h))) = h
        rw [MulEquiv.apply_symm_apply, algEquivConjHom_apply_apply_symm e h]
      map_mul' := by
        intro g g'
        show algEquivConjHom e (ϕ (g * g')) =
          algEquivConjHom e (ϕ g) * algEquivConjHom e (ϕ g')
        rw [map_mul, map_mul] }
  have hψeq : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g) := fun g => rfl
  have hψ : IsHomeomorph ψ := by
    have h2 : IsHomeomorph (algEquivConjHom e) := isHomeomorph_algEquivConjHom e
    rw [show ⇑ψ = ⇑(algEquivConjHom e) ∘ ⇑ϕ from rfl]
    exact h2.comp hϕ
  -- ## Step 5: transport the local correspondence and the Frobenius correspondence
  obtain ⟨a', ha'⟩ := localCorrespondence_conj ϕ a e ψ hψeq
  have b' : FrobeniusCorrespondencePlace ψ hψ a' :=
    exists_frobeniusCorrespondence_transport ϕ hϕ a b e ψ hψeq hψ a' ha'
  -- ## Step 6: the level-pair bridge at the base-changed isomorphism
  have hlevθ : NK.ReconstructField.LevelIsoInput
      (baseChangeGalEquiv A B eA hA eB hB ψ)
      (isHomeomorph_baseChangeGalEquiv A B eA hA eB hB ψ hψ) :=
    levelIsoInput_of_localCorrespondence_fourf5 (Ω := K₁') A B ℓ
      (baseChangeGalEquiv A B eA hA eB hB ψ)
      (isHomeomorph_baseChangeGalEquiv A B eA hA eB hB ψ hψ)
      (localCorrespondence_baseChange A B eA hA eB hB ψ a')
      (frobeniusCorrespondencePlace_baseChange A B eA hA eB hB ψ hψ a' b')
      h45 hc
  -- ## Step 7: transport the level-wise input back to `ϕ`
  have hlevψ : NK.ReconstructField.LevelIsoInput ψ hψ :=
    levelIsoInput_baseChange A B eA hA eB hB ψ hψ hlevθ
  have hlevϕ : NK.ReconstructField.LevelIsoInput ϕ hϕ :=
    levelIsoInput_transport ϕ hϕ e ψ hψeq hψ hlevψ
  exact NK.Mine.exists_sigma_of_localCorrespondence ϕ hϕ a hlevϕ

/-- **The `∃!` form of the σ-producing step on the corrected rank hypothesis.**

The existence half is `exists_sigma_of_localCorrespondence_corrected`; uniqueness is the *proved*
`Submission.NeukirchUchida.unique_sigma`.  The conclusion is written with
`NK.ReconstructEndgame`'s spelling (`MapsBase` ∧ the conjugation identity), which is
definitionally `Submission.NeukirchUchida.Conjugates`. -/
theorem neukirch_uchida_of_localCorrespondence_corrected {K₁ K₂ K₁' K₂' : Type*} [Field K₁]
    [NumberField K₁] [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [Algebra ℚ K₁']
    [IsGalois ℚ K₁'] [IsSepClosure ℚ K₁'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : NK.Reconstruct.Fourf5InputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  obtain ⟨σ, hσ⟩ := exists_sigma_of_localCorrespondence_corrected ϕ hϕ a b ℓ h45 hc
  exact ⟨σ, hσ, fun y hy => Submission.NeukirchUchida.unique_sigma ϕ hϕ hy hσ⟩

/-- **The `∃!` form of the σ-producing step on the corrected rank hypothesis**, stated with
`Submission.NeukirchUchida.Conjugates` (the form used by `Submission.NeukirchUchida.neukirch_uchida_core`). -/
theorem existsUnique_conjugates_of_localCorrespondence_corrected {K₁ K₂ K₁' K₂' : Type*}
    [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    [Algebra ℚ K₁'] [IsGalois ℚ K₁'] [IsSepClosure ℚ K₁'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : NK.Reconstruct.Fourf5InputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁') :
    ∃! σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ⟩ := exists_sigma_of_localCorrespondence_corrected ϕ hϕ a b ℓ h45 hc
  exact ⟨σ, hσ, fun y hy => Submission.NeukirchUchida.unique_sigma ϕ hϕ hy hσ⟩

/-- **The existence half on the corrected residual** `NK.RankTheoryDeep.CorrectedResidualsDeep`
(in the ambient `ℚ`-algebra vocabulary).  The single rank hypothesis is the corrected residual,
whose fields are named classical theorems; Shimizu's Proposition 4f.5 is derived from it by
`NK.EndgameRepair.fourf5Gen_of_correctedResidualsDeep`. -/
theorem exists_sigma_of_correctedResidualsDeep {K₁ K₂ K₁' K₂' : Type*} [Field K₁]
    [NumberField K₁] [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [Algebra ℚ K₁']
    [IsGalois ℚ K₁'] [IsSepClosure ℚ K₁'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (hres : NK.RankTheoryDeep.CorrectedResidualsDeep K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_localCorrespondence_corrected ϕ hϕ a b ℓ
    (fourf5Gen_of_correctedResidualsDeep hres) hc

/-- **The `∃!` form on the corrected residual** (ambient `ℚ`-algebra vocabulary). -/
theorem neukirch_uchida_of_correctedResidualsDeep {K₁ K₂ K₁' K₂' : Type*} [Field K₁]
    [NumberField K₁] [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [Algebra ℚ K₁']
    [IsGalois ℚ K₁'] [IsSepClosure ℚ K₁'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (hres : NK.RankTheoryDeep.CorrectedResidualsDeep K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  obtain ⟨σ, hσ, huniq⟩ :=
    neukirch_uchida_of_localCorrespondence_corrected ϕ hϕ a b ℓ
      (fourf5Gen_of_correctedResidualsDeep hres) hc
  exact ⟨σ, hσ, huniq⟩

end Main

section Derived

/-! ## The repaired σ-producing step with the `ℚ`-structure derived

The theorems of this section carry **no** `ℚ`-algebra hypothesis on `K₁'`: the structure
`NK.ReconstructEndgame.ratAlgebra K₁ K₁'`, the instance `IsSepClosure ℚ K₁'` and (through it)
`IsGalois ℚ K₁'` are derived from `[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`, and
the rank and Čebotarev hypotheses are stated in the derived forms
`NK.EndgameRepair.Fourf5InputGenDerived` and
`NK.ReconstructEndgame.ChebotarevInputDerived`. -/

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The existence half, with `Fourf5InputGen` in the derived `ℚ`-algebra vocabulary.** -/
theorem exists_sigma_of_localCorrespondence_corrected_derived
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : Fourf5InputGenDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  letI : Algebra ℚ K₁' := NK.ReconstructEndgame.ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' :=
    NK.ReconstructEndgame.isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := NK.ReconstructEndgame.isGalois_rat_of_numberField K₁ K₁'
  exact exists_sigma_of_localCorrespondence_corrected ϕ hϕ a b ℓ h45 hc

/-- **The `∃!` form, with `Fourf5InputGen` in the derived `ℚ`-algebra vocabulary.** -/
theorem neukirch_uchida_of_localCorrespondence_corrected_derived
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : Fourf5InputGenDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  obtain ⟨σ, hσ⟩ := exists_sigma_of_localCorrespondence_corrected_derived ϕ hϕ a b ℓ h45 hc
  exact ⟨σ, hσ, fun y hy => Submission.NeukirchUchida.unique_sigma ϕ hϕ hy hσ⟩

end Derived

section DerivedResidual

/-! ## The repaired σ-producing step on the **corrected residual**, derived `ℚ`-structure

`NK.RankTheoryDeep.CorrectedResidualsDerived K K' ℓ` is stated for `K`, `K'` in a *common*
universe (as is `NK.Mine.ResidualsDerived`), so these two theorems are stated with
`K₁, K₁' : Type u` and `K₂, K₂' : Type v`. -/

universe u v

variable {K₁ K₁' : Type u} {K₂ K₂' : Type v} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The repaired existence half on the corrected residual, in the derived vocabulary.**

This is the intended replacement of the rank hypothesis of
`NK.Mine.neukirch_uchida_of_localStructureData_residuals` and of the Shimizu-rank consumers of
`Submission/Work/ShimizuRank/Package.lean`: the single rank hypothesis is
`NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ`, i.e. the corrected residual in the same
derived `ℚ`-algebra vocabulary, and Shimizu's Proposition 4f.5 is obtained from it by
`NK.EndgameRepair.fourf5GenDerived_of_correctedResidualsDerived`
(=`NK.RankTheoryDeep.fourf5Gen_of_correctedResidualsDeep`). -/
theorem exists_sigma_of_correctedResiduals
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (hres : NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_localCorrespondence_corrected_derived ϕ hϕ a b ℓ
    (fourf5GenDerived_of_correctedResidualsDerived hres) hc

/-- **The `∃!` form on the corrected residual, in the derived vocabulary.**

This is the repaired counterpart of the `∃!` capstone of the Shimizu route: CoNF XII Thm 12.2.1 for
the place correspondence (a) and the Frobenius correspondence (b), with the rank theory reduced to
`NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ`. -/
theorem neukirch_uchida_of_correctedResiduals
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (hres : NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  obtain ⟨σ, hσ⟩ := exists_sigma_of_correctedResiduals ϕ hϕ a b ℓ hres hc
  exact ⟨σ, hσ, fun y hy => Submission.NeukirchUchida.unique_sigma ϕ hϕ hy hσ⟩

end DerivedResidual

end NK.EndgameRepair
