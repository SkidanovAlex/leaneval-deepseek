import Mathlib
import Submission.Work.DeltaHomology.SkelInclDefs
import Submission.Work.DeltaHomology.skelQuotient_X_isZero
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.SkeletonMap
import Submission.Work.DeltaHomology.isZero_chainX_of_dim_lt
import Submission.Work.DeltaHomology.CellClassMap
import Submission.Work.DeltaHomology.cellClassMapCell_isIso
import Submission.Work.DeltaHomology.isIso_fold_cellClassMap
import Submission.Work.DeltaHomology.isIso_relHomologyMap_cellIntoNeighbourhood
import Submission.Work.DeltaHomology.relHomology_punctSkel_succ_iso
import Submission.Work.DeltaHomology.openCoverInclPair
import Submission.Work.HomologyExtra.Main
import Submission.Work.HomologyExtra.CycleClass
import Submission.Work.HomologyExtra.RelChainMapFunctor
import Submission.Work.DeltaHomology.skelQuotient_desc_f_component
import Submission.Work.DeltaHomology.simplexRelChain_relChainMap_chiInSkelSet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

set_option backward.isDefEq.respectTransparency false

namespace Work.DeltaHomology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-- The punctured `n`-skeleton `Xⁿ ∖ {barycentres}`, as a subset of the `n`-skeleton. -/
abbrev punctPiece (R : DeltaRealization K X) (n : ℕ) : Set ↥(R.toDeltaSimplexMap.skelSet n) :=
  {x | (x : X) ∈ R.toDeltaSimplexMap.punctSkel n}

/-- The relative chain complex of the pair `(Xⁿ, Xⁿ ∖ {barycentres})`. -/
abbrev relCx (R : DeltaRealization K X) (n : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  relChain ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet n)) (punctPiece R n)

/-- The quotient of the `(k+1)`-skeleton chain complex by the `k`-skeleton chain complex. -/
abbrev skelQuotientCx (K : DeltaCx) (k : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))

/-! ## A criterion for a fold map out of a biproduct of copies of `ℤ` to be an isomorphism -/

/-- **Criterion.**  If `f σ : ℤ ⟶ Y` and `g σ : Y ⟶ ℤ` satisfy that `f σ ≫ g σ` is an
isomorphism for every `σ` and that `f σ ≫ g ρ = 0` for `σ ≠ ρ`, and if `Y` is (abstractly)
isomorphic to `∐_σ ℤ`, then `biproduct.desc f` is an isomorphism.

The proof is the "Hopfian"/Orzech argument: `F := biproduct.desc f` is a split monomorphism and
`G := biproduct.lift (fun σ => g σ ≫ inv (f σ ≫ g σ))` satisfies `F ≫ G = 𝟙`; conjugating `G`
by the isomorphism `e` gives a *surjective* endomorphism of the finitely generated module
`∐_σ ℤ`, which is therefore injective (Orzech property of `ℤ`), hence an isomorphism. -/
theorem isIso_biproduct_desc_of_isIso_comp {N : ℕ} {Y : ModuleCat ℤ}
    (f : Fin N → (ModuleCat.of ℤ ℤ ⟶ Y)) (g : Fin N → (Y ⟶ ModuleCat.of ℤ ℤ))
    (h1 : ∀ σ, IsIso (f σ ≫ g σ)) (h2 : ∀ σ ρ, σ ≠ ρ → f σ ≫ g ρ = 0)
    (e : Y ≅ ⨁ fun _ : Fin N => ModuleCat.of ℤ ℤ) :
    IsIso (biproduct.desc f) := by
  classical
  let g' : Fin N → (Y ⟶ ModuleCat.of ℤ ℤ) :=
    fun σ => g σ ≫ inv (f σ ≫ g σ)
  have h1' : ∀ σ, f σ ≫ g' σ = 𝟙 (ModuleCat.of ℤ ℤ) := by
    intro σ
    haveI := h1 σ
    simp only [g']
    rw [← Category.assoc, IsIso.hom_inv_id]
  have h2' : ∀ σ ρ, σ ≠ ρ → f σ ≫ g' ρ = 0 := by
    intro σ ρ h
    simp only [g']
    rw [← Category.assoc, h2 σ ρ h, zero_comp]
  let F : (⨁ fun _ : Fin N => ModuleCat.of ℤ ℤ) ⟶ Y := biproduct.desc f
  let G : Y ⟶ (⨁ fun _ : Fin N => ModuleCat.of ℤ ℤ) := biproduct.lift g'
  have hFG : F ≫ G = 𝟙 _ := by
    have hlift : biproduct.lift g' =
        ∑ σ, g' σ ≫ biproduct.ι (fun _ : Fin N => ModuleCat.of ℤ ℤ) σ := by
      rw [← Category.comp_id (biproduct.lift g'),
        ← biproduct.total (f := fun _ : Fin N => ModuleCat.of ℤ ℤ), Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Category.assoc, biproduct.lift_π]
    show biproduct.desc f ≫ G = 𝟙 _
    rw [show G = biproduct.lift g' from rfl, hlift, Preadditive.comp_sum]
    apply biproduct.hom_ext'
    intro i
    rw [Preadditive.comp_sum]
    have hterm : ∀ j, biproduct.ι (fun _ : Fin N => ModuleCat.of ℤ ℤ) i ≫
        (biproduct.desc f ≫ g' j ≫ biproduct.ι (fun _ : Fin N => ModuleCat.of ℤ ℤ) j)
        = if j = i then biproduct.ι (fun _ : Fin N => ModuleCat.of ℤ ℤ) i else 0 := by
      intro j
      rw [← Category.assoc, biproduct.ι_desc]
      by_cases hij : j = i
      · subst hij
        rw [← Category.assoc, h1' j, Category.id_comp, ite_eq_left rfl]
      · rw [← Category.assoc, h2' i j (Ne.symm hij), zero_comp, ite_eq_right hij]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Category.comp_id,
      Finset.sum_ite_eq' Finset.univ i
        fun _ => biproduct.ι (fun _ : Fin N => ModuleCat.of ℤ ℤ) i]
    simp
  haveI : Module.Finite ℤ (↑(⨁ fun _ : Fin N => ModuleCat.of ℤ ℤ)) := by
    have hb : Function.Bijective
        (ModuleCat.biproductIsoPi (fun _ : Fin N => ModuleCat.of ℤ ℤ)).inv.hom :=
      ConcreteCategory.bijective_of_isIso _
    exact Module.Finite.of_surjective _ hb.surjective
  haveI : IsSplitEpi G := IsSplitEpi.mk ⟨SplitEpi.mk F hFG⟩
  have hGepi : Epi G := IsSplitEpi.epi G
  let v : (⨁ fun _ : Fin N => ModuleCat.of ℤ ℤ) ⟶
      (⨁ fun _ : Fin N => ModuleCat.of ℤ ℤ) := e.inv ≫ G
  have hvsurj : Function.Surjective v.hom := by
    rw [← ModuleCat.epi_iff_surjective]
    exact inferInstance
  have hv : IsIso v := (ConcreteCategory.isIso_iff_bijective v).mpr
    ⟨OrzechProperty.injective_of_surjective_endomorphism v.hom hvsurj, hvsurj⟩
  have hG' : G = e.hom ≫ v := by
    show G = e.hom ≫ (e.inv ≫ G)
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hcancel : F ≫ e.hom = inv v := by
    apply (cancel_mono v).1
    have h1v : (F ≫ e.hom) ≫ v = 𝟙 _ := by rw [Category.assoc, ← hG', hFG]
    exact h1v.trans (IsIso.inv_hom_id v).symm
  have hF : F = inv v ≫ e.inv := by
    have h2 : F = F ≫ (e.hom ≫ e.inv) := by rw [Iso.hom_inv_id, Category.comp_id]
    rw [h2, ← Category.assoc, hcancel]
  rw [show biproduct.desc f = F from rfl, hF]
  haveI := hv
  infer_instance

/-- The cell pair `(cell_σ, punctCell_σ)` has homology `ℤ` in degree `n`. -/
theorem nonempty_cellPairHomology_iso_zmod {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    Nonempty (relHomology ZMod n (TopCat.of (R.toDeltaSimplexMap.cell n σ))
      (cellPunctPiece R n σ) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e₁⟩ := cell_relHomology_iso R n σ n
  rw [ite_eq_left rfl] at e₁
  obtain ⟨e₀⟩ := relHomology_iso_of_homeomorph
    (Homeomorph.refl (TopCat.of (R.toDeltaSimplexMap.cell n σ)))
    (A := cellPunctPiece R n σ)
    (B := {x : ↥(R.toDeltaSimplexMap.cell n σ) |
      (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ})
    (fun x => by rw [cellPunctPiece_eq_compl_singleton]; exact Iff.rfl) n
  exact ⟨e₀ ≪≫ e₁⟩

end

end Work.DeltaHomology



namespace Work.DeltaHomology

namespace Work.DeltaHomology

theorem isIso_homologyMap_skelQuotient_desc {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k : ℕ)
    (hzero : DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))
      ≫ (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
          ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
              {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
                (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) = 0) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.desc (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
        (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
          ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
              {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
                (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) hzero) (k + 1)) := by
  classical
  let Q : ChainComplex (ModuleCat ℤ) ℕ := skelQuotientCx K k
  let πQ : (K.skel (k + 1)).chain ⟶ Q :=
    cokernel.π (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
  let τ : Q ⟶ relCx R (k + 1) :=
    cokernel.desc (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
      (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
        ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
            {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
              (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) hzero
  show IsIso (HomologicalComplex.homologyMap τ (k + 1))
  have hnext : (ComplexShape.down ℕ).next (k + 1) = k := by
    apply ComplexShape.next_eq'
    simp [ComplexShape.down, ComplexShape.down']
  have hprev : (ComplexShape.down ℕ).prev (k + 1) = k + 2 := by
    apply ComplexShape.prev_eq'
    simp [ComplexShape.down, ComplexShape.down']
  have hQk : IsZero (Q.X k) := skelQuotient_X_isZero K k (by omega)
  have hQk2 : IsZero (Q.X (k + 2)) := skelQuotient_X_isZero K k (by omega)
  have hdk : Q.d (k + 1) k = 0 := hQk.eq_of_tgt _ _
  have hdk2 : Q.d (k + 2) (k + 1) = 0 := hQk2.eq_of_src _ _
  haveI hiCyc : IsIso (Q.iCycles (k + 1)) :=
    HomologicalComplex.isIso_iCycles Q (k + 1) k hnext hdk
  haveI hhomπ : IsIso (Q.homologyπ (k + 1)) :=
    HomologicalComplex.isIso_homologyπ Q (k + 2) (k + 1) hprev hdk2
  let u : Fin (K.card (k + 1)) → (ModuleCat.of ℤ ℤ ⟶ Q.X (k + 1)) :=
    fun σ => (K.skel (k + 1)).chainι (k + 1)
        (Fin.cast (DeltaCx.skel_card_eq K (k + 1) le_rfl).symm σ)
      ≫ (πQ).f (k + 1)
  have hu : ∀ σ, u σ ≫ Q.d (k + 1) ((ComplexShape.down ℕ).next (k + 1)) = 0 := by
    intro σ
    rw [hnext, hdk, comp_zero]
  let FQ : (⨁ fun _ : Fin (K.card (k + 1)) => ModuleCat.of ℤ ℤ) ⟶ Q.homology (k + 1) :=
    biproduct.desc (fun σ => Work.HomologyExtra.cycleClass (u σ) (hu σ))
  obtain ⟨eY⟩ := relHomology_punctSkel_succ_iso R k (k + 1)
  rw [ite_eq_left rfl] at eY
  let e := eY ≪≫ (biproduct.isoCoproduct
    (fun _ : Fin (K.card (k + 1)) => ModuleCat.of ℤ ℤ)).symm
  have hqiso : ∀ σ : Fin (K.card (k + 1)),
      IsIso (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)) :=
    fun σ => isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) σ
  have hf1 : ∀ σ, IsIso ((Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMap R (k + 1) σ) ≫ (relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ) ≫ @CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) σ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.hom)) := by
    intro σ
    haveI hq : IsIso (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)) :=
      hqiso σ
    haveI hkap : IsIso ((nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.hom) :=
      (nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.isIso_hom
    have hcc := cellClassMap_comp_punctSkelToNeighbourhood R (k + 1) σ
    have hstep : (Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMap R (k + 1) σ) ≫ (relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ) ≫ @CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) σ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.hom)
        = Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMapCell R (k + 1) σ ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.hom := by
      calc (Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMap R (k + 1) σ) ≫ (relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ) ≫ @CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) σ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.hom)
          = (Work.HomologyExtra.simplexGenMap (k + 1) ≫ (cellClassMap R (k + 1) σ ≫ relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ))) ≫ (@CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) σ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.hom) := by simp only [Category.assoc]
        _ = (Work.HomologyExtra.simplexGenMap (k + 1) ≫ (cellClassMapCell R (k + 1) σ ≫ relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ))) ≫ (@CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) σ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.hom) := by rw [hcc]
        _ = Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMapCell R (k + 1) σ ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) σ).some.hom := by
              simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [hstep]
    haveI := Work.HomologyExtra.isIso_simplexGenMap_all (k + 1)
    haveI := cellClassMapCell_isIso R (k + 1) σ
    infer_instance
  have hf2 : ∀ σ ρ, σ ≠ ρ → ((Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMap R (k + 1) σ)
      ≫ (relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) ρ) ≫ @CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) ρ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) ρ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) ρ).some.hom)) = 0 := by
    intro σ ρ h
    have hz := cellClassMap_comp_punctSkelToNeighbourhood_eq_zero R k (σ := ρ) (τ := σ) h
    calc (Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMap R (k + 1) σ) ≫ (relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) ρ) ≫ @CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) ρ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) ρ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) ρ).some.hom)
        = (Work.HomologyExtra.simplexGenMap (k + 1) ≫ (cellClassMap R (k + 1) σ ≫ relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) ρ))) ≫ (@CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) ρ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) ρ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) ρ).some.hom) := by simp only [Category.assoc]
      _ = (Work.HomologyExtra.simplexGenMap (k + 1) ≫ 0) ≫ (@CategoryTheory.inv _ _ _ _ (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) ρ)) (isIso_relHomologyMap_cellIntoNeighbourhood R (k + 1) ρ) ≫ (nonempty_cellPairHomology_iso_zmod R (k + 1) ρ).some.hom) := by rw [hz]
      _ = 0 := by simp
  have hfold : IsIso (biproduct.desc (fun σ : Fin (K.card (k + 1)) => Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMap R (k + 1) σ)) :=
    isIso_biproduct_desc_of_isIso_comp _ _ hf1 hf2 e
  -- the two folds agree componentwise
  have hkey : ∀ σ, Work.HomologyExtra.cycleClass (u σ) (hu σ)
      ≫ HomologicalComplex.homologyMap τ (k + 1) = Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMap R (k + 1) σ := by
    intro σ
    have hchain : u σ ≫ τ.f (k + 1) = SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1))))
          (DeltaSimplexMap.chiInSkelSet R.toDeltaSimplexMap (k + 1) le_rfl σ)
        ≫ (relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
            {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
              (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}).f (k + 1) :=
      _root_.Work.DeltaHomology.Work.DeltaHomology.skelQuotient_desc_f_component R k hzero σ
    have hdc := _root_.Work.DeltaHomology.Work.DeltaHomology.simplexRelChain_relChainMap_chiInSkelSet R (k + 1) σ
    have h1 : Work.HomologyExtra.cycleClass (u σ) (hu σ)
          ≫ HomologicalComplex.homologyMap τ (k + 1)
        = Work.HomologyExtra.cycleClass (u σ ≫ τ.f (k + 1)) _ :=
      Work.HomologyExtra.cycleClass_naturality τ (u σ) (hu σ)
    have h2 : Work.HomologyExtra.cycleClass (Work.HomologyExtra.simplexRelChain (k + 1))
            (Work.HomologyExtra.simplexRelChain_d (k + 1))
          ≫ HomologicalComplex.homologyMap (relChainMap ZMod ((R.skelPunctPairHom (k + 1) σ).comp (pairHomOfSubset (stdSimplexBoundary_subset_punctStdSimplex (k + 1))))) (k + 1)
        = Work.HomologyExtra.cycleClass ((Work.HomologyExtra.simplexRelChain (k + 1)) ≫
            (relChainMap ZMod ((R.skelPunctPairHom (k + 1) σ).comp (pairHomOfSubset (stdSimplexBoundary_subset_punctStdSimplex (k + 1))))).f (k + 1)) _ :=
      Work.HomologyExtra.cycleClass_naturality (relChainMap ZMod ((R.skelPunctPairHom (k + 1) σ).comp (pairHomOfSubset (stdSimplexBoundary_subset_punctStdSimplex (k + 1)))))
        (Work.HomologyExtra.simplexRelChain (k + 1))
        (Work.HomologyExtra.simplexRelChain_d (k + 1))
    rw [h1]
    rw [show Work.HomologyExtra.simplexGenMap (k + 1) = Work.HomologyExtra.cycleClass (Work.HomologyExtra.simplexRelChain (k + 1))
        (Work.HomologyExtra.simplexRelChain_d (k + 1)) from rfl]
    rw [show cellClassMap R (k + 1) σ = HomologicalComplex.homologyMap (relChainMap ZMod (pairHomOfSubset (stdSimplexBoundary_subset_punctStdSimplex (k + 1)))) (k + 1)
          ≫ HomologicalComplex.homologyMap (relChainMap ZMod (R.skelPunctPairHom (k + 1) σ)) (k + 1) from rfl]
    rw [← HomologicalComplex.homologyMap_comp]
    rw [← Work.HomologyExtra.relChainMap_comp]
    rw [h2]
    exact Work.HomologyExtra.cycleClass_eq _ _ (hchain.trans hdc.symm)
  have hcompfold : FQ ≫ HomologicalComplex.homologyMap τ (k + 1)
      = biproduct.desc (fun σ : Fin (K.card (k + 1)) => Work.HomologyExtra.simplexGenMap (k + 1) ≫ cellClassMap R (k + 1) σ) := by
    show biproduct.desc (fun σ => Work.HomologyExtra.cycleClass (u σ) (hu σ))
        ≫ HomologicalComplex.homologyMap τ (k + 1) = _
    apply biproduct.hom_ext'
    intro σ
    rw [← Category.assoc, biproduct.ι_desc, biproduct.ι_desc]
    exact hkey σ
  -- `FQ` is an isomorphism
  have hFQ : IsIso FQ := by
    have hcyc : ∀ σ, Work.HomologyExtra.cycleClass (u σ) (hu σ)
        = u σ ≫ (inv (Q.iCycles (k + 1)) ≫ Q.homologyπ (k + 1)) := by
      intro σ
      have hL : Q.liftCycles (u σ) ((ComplexShape.down ℕ).next (k + 1)) rfl (hu σ)
          = u σ ≫ inv (Q.iCycles (k + 1)) := by
        rw [← Category.comp_id (Q.liftCycles (u σ) ((ComplexShape.down ℕ).next (k + 1)) rfl (hu σ)),
          ← IsIso.hom_inv_id (Q.iCycles (k + 1)), ← Category.assoc,
          HomologicalComplex.liftCycles_i]
      calc Work.HomologyExtra.cycleClass (u σ) (hu σ)
          = Q.liftCycles (u σ) ((ComplexShape.down ℕ).next (k + 1)) rfl (hu σ)
              ≫ Q.homologyπ (k + 1) := rfl
        _ = (u σ ≫ inv (Q.iCycles (k + 1))) ≫ Q.homologyπ (k + 1) := by rw [hL]
        _ = u σ ≫ (inv (Q.iCycles (k + 1)) ≫ Q.homologyπ (k + 1)) := by rw [Category.assoc]
    have hdesc : FQ = biproduct.desc (fun σ => u σ)
        ≫ (inv (Q.iCycles (k + 1)) ≫ Q.homologyπ (k + 1)) := by
      show biproduct.desc (fun σ => Work.HomologyExtra.cycleClass (u σ) (hu σ)) = _
      rw [show (fun σ => Work.HomologyExtra.cycleClass (u σ) (hu σ))
          = (fun σ => u σ ≫ (inv (Q.iCycles (k + 1)) ≫ Q.homologyπ (k + 1)))
            from funext hcyc]
      apply biproduct.hom_ext'
      intro σ
      rw [← Category.assoc, biproduct.ι_desc, biproduct.ι_desc]
    rw [hdesc]
    haveI : IsIso (inv (Q.iCycles (k + 1)) ≫ Q.homologyπ (k + 1)) := inferInstance
    haveI : IsIso (biproduct.desc (fun σ => u σ)) := by
      have hπ : IsIso ((πQ).f (k + 1)) := by
        let E := PreservesCokernel.iso
          (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) (k + 1))
          (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
        haveI : IsIso E.inv := inferInstance
        have hfac : (πQ).f (k + 1)
            = cokernel.π ((DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f (k + 1)) ≫ E.inv := by
          have h : (πQ).f (k + 1) ≫ E.hom
              = cokernel.π ((DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f (k + 1)) :=
            PreservesCokernel.π_iso_hom
              (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) (k + 1))
              (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
          rw [← Category.comp_id ((πQ).f (k + 1))]
          rw [show 𝟙 (Q.X (k + 1)) = E.hom ≫ E.inv from (Iso.hom_inv_id E).symm]
          rw [← Category.assoc]
          rw [show (πQ).f (k + 1) ≫ E.hom
              = cokernel.π ((DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f (k + 1)) from h]
        rw [hfac]
        haveI : IsIso (cokernel.π
            ((DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f (k + 1))) := by
          have hgsrc : IsZero ((K.skel k).chainX (k + 1)) :=
            isZero_chainX_of_dim_lt (K.skel k) (by rw [DeltaCx.skel_dim]; omega)
          have hg0 : (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))).f (k + 1) = 0 :=
            hgsrc.eq_of_src _ _
          rw [hg0, ← CategoryTheory.Limits.cokernelZeroIsoTarget_inv]
          infer_instance
        infer_instance
      have hbase : IsIso (biproduct.desc (fun σ : Fin (K.card (k + 1)) =>
          (K.skel (k + 1)).chainι (k + 1)
            (Fin.cast (DeltaCx.skel_card_eq K (k + 1) le_rfl).symm σ))) := by
        have heq : biproduct.desc (fun σ : Fin (K.card (k + 1)) =>
              (K.skel (k + 1)).chainι (k + 1)
                (Fin.cast (DeltaCx.skel_card_eq K (k + 1) le_rfl).symm σ))
            = (biproduct.whiskerEquiv (finCongr (DeltaCx.skel_card_eq K (k + 1) le_rfl).symm)
                (fun _ => Iso.refl (ModuleCat.of ℤ ℤ))).hom
              ≫ (biproduct.isoCoproduct
                  (fun _ : Fin ((K.skel (k + 1)).card (k + 1)) => ModuleCat.of ℤ ℤ)).hom := by
          apply biproduct.hom_ext'
          intro σ
          rw [biproduct.whiskerEquiv_hom]
          rw [← Category.assoc, biproduct.ι_desc, biproduct.isoCoproduct_hom,
            biproduct.ι_desc]
          rw [Iso.refl_inv, Category.id_comp, biproduct.ι_desc]
          rfl
        rw [heq]
        infer_instance
      rw [show biproduct.desc (fun σ => u σ)
          = biproduct.desc (fun σ : Fin (K.card (k + 1)) => (K.skel (k + 1)).chainι (k + 1)
              (Fin.cast (DeltaCx.skel_card_eq K (k + 1) le_rfl).symm σ)) ≫ (πQ).f (k + 1) from ?_]
      · infer_instance
      · apply biproduct.hom_ext'
        intro σ
        rw [← Category.assoc, biproduct.ι_desc, biproduct.ι_desc]
    infer_instance
  haveI := hFQ
  haveI : IsIso (FQ ≫ HomologicalComplex.homologyMap τ (k + 1)) := by
    rw [hcompfold]; exact hfold
  rw [← Category.id_comp (HomologicalComplex.homologyMap τ (k + 1)), ← IsIso.inv_hom_id FQ,
    Category.assoc, hcompfold]
  infer_instance

end Work.DeltaHomology

end Work.DeltaHomology

namespace Work.DeltaHomology

/-- **The cokernel comparison map is an isomorphism on the top relative homology** (flat name).

The statement above is registered in the namespace `Work.DeltaHomology.Work.DeltaHomology` (the
file carries two identical `namespace Work.DeltaHomology` lines, as it was delivered); this is the
same lemma under the flat name by which the rest of the project refers to it. -/
theorem isIso_homologyMap_skelQuotient_desc {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k : ℕ)
    (hzero : DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))
      ≫ (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
          ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
              {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
                (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) = 0) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.desc (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
        (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
          ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
              {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
                (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) hzero) (k + 1)) :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.isIso_homologyMap_skelQuotient_desc R k hzero

end Work.DeltaHomology
