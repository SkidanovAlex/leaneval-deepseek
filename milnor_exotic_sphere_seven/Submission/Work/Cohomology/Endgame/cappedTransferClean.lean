import Mathlib
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Milnor.mkToVkRangeHomeomorph
import Submission.Work.Milnor.cohomology_Mk_minus_two
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Cohomology.pairIsoOfTrivial
import Submission.Work.Cohomology.CompatIso.smallIsoHom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The capped-manifold transfer, fork-clean

A self-contained copy of the transfer lemmas of
`Submission/Work/Cohomology/capped_rel_cupSquare_ne_zero.lean` (a colleague's file) with two
modifications:

* the import of `Submission.Work.Cohomology.vk_cupSquare_ne_zero` is **removed** (that import pulls
  in `Submission.Work.Cohomology.Crux.vk_relCapPair_surjective`, which does not currently compile
  and therefore poisons every module that reaches it), together with the three declarations at the
  end of the original file that used the crux;
* the declarations are put in the namespace `Work.Cohomology.Endgame.CappedTransfer` (rather than
  `Work.Cohomology`) so that they can never clash with the originals if both are ever imported
  together.

What remains is exactly the transfer apparatus used by `Endgame/cappedEndgame.lean`: the
surjectivity `epi_capRelMap` of the relative restriction `H⁴(X,A) → H⁴(Vk(-2), Mk(-2))` along `ιX`,
and the compatibility `relCupHNatural_capPair` of that restriction with the relative cup product.
-/

namespace Work.Cohomology.Endgame.CappedTransfer

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-! ## Elementary helpers -/

/-- An isomorphism of `ℤ`-modules is surjective. -/
lemma surjective_of_isIso {A B : ModuleCat ℤ} (f : A ⟶ B) [IsIso f] :
    Function.Surjective f.hom :=
  (ModuleCat.epi_iff_surjective f).mp inferInstance

/-- An isomorphism of `ℤ`-modules is injective. -/
lemma injective_of_isIso {A B : ModuleCat ℤ} (f : A ⟶ B) [IsIso f] :
    Function.Injective f.hom :=
  (ModuleCat.mono_iff_injective f).mp inferInstance

/-- The composition of two surjections of `ℤ`-modules is surjective. -/
lemma surjective_comp {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Surjective f.hom) (hg : Function.Surjective g.hom) :
    Function.Surjective (f ≫ g).hom := by
  intro y
  obtain ⟨z, hz⟩ := hg y
  obtain ⟨w, hw⟩ := hf z
  exact ⟨w, by rw [ModuleCat.comp_apply, hw, hz]⟩

/-- A homeomorphism of spaces induces an isomorphism on singular cohomology. -/
lemma isIso_singularCohomologyMap_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    IsIso (singularCohomologyMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.isoOfHomeo e).hom n) := by
  refine IsIso.mk ⟨singularCohomologyMap ℤ (TopCat.of Y) (TopCat.of X)
    (TopCat.isoOfHomeo e).inv n, ?_, ?_⟩
  · rw [← singularCohomologyMap_comp, Iso.inv_hom_id, singularCohomologyMap_id]
  · rw [← singularCohomologyMap_comp, Iso.hom_inv_id, singularCohomologyMap_id]

/-- The first projection of a biproduct of cochain complexes is an epimorphism on homology. -/
lemma epi_homologyMap_biprod_fst (K L : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    Epi (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) k) := by
  haveI : IsSplitEpi (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) k) :=
    IsSplitEpi.mk' ⟨HomologicalComplex.homologyMap (biprod.inl : K ⟶ K ⊞ L) k, by
      rw [← HomologicalComplex.homologyMap_comp, biprod.inl_fst,
        HomologicalComplex.homologyMap_id]⟩
  infer_instance

/-- The first component of `mvCochainF` is the dual of `smallOfU`, globally. -/
lemma mvCochainF_comp_fst {X : TopCat} (U V : Set X) :
    mvCochainF U V ≫ (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V)
      = dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥U)) (smallChains U V) (smallOfU U V) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, mvCochainF_fst]

/-- **Naturality of the inclusion of the relative cochain complex.**  For a map of pairs
`(X₁,A₁) → (X₂,A₂)`, the induced map on relative cochains is compatible with the inclusions into
the absolute cochain complexes. -/
lemma relComplexMap_comp_relIncl {R : Type} [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁)
    (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap R A₁ A₂ f h ≫ relIncl R X₁ A₁ = relIncl R X₂ A₂ ≫ dualChainMap R X₁ X₂ f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relComplexMap_f, relIncl_f, relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact relMapLM_coe R A₁ A₂ f h n x

/-! ## The pieces of the capped space -/

/-- The homeomorphism `Vk (-2) ≅ glueU D` induced by the open embedding `ιX`. -/
abbrev eU (D : Work.Milnor.CapData) :
    Submission.Milnor.Vk (-2) ≃ₜ ↥(Work.Milnor.glueU D) :=
  D.isOpenEmbedding_ιX.toIsEmbedding.toHomeomorph

/-- The corresponding map of topological spaces `Vk (-2) → glueU D`. -/
abbrev fU (D : Work.Milnor.CapData) :
    TopCat.of (Submission.Milnor.Vk (-2)) ⟶ TopCat.of ↥(Work.Milnor.glueU D) :=
  (TopCat.isoOfHomeo (eU D)).hom

/-- The map of pairs `(Vk (-2), Mk (-2)) → (X, A)` given by `ιX`. -/
abbrev capPairMap (D : Work.Milnor.CapData) :
    TopCat.of (Submission.Milnor.Vk (-2)) ⟶ Work.Milnor.glueX D :=
  TopCat.ofHom ⟨D.ιX, D.continuous_ιX⟩

/-- The underlying point of `eU D x`. -/
lemma eU_apply_coe (D : Work.Milnor.CapData) (x : Submission.Milnor.Vk (-2)) :
    ((eU D x : ↥(Work.Milnor.glueU D)) : Work.Milnor.cappedSpace D) = D.ιX x :=
  D.isOpenEmbedding_ιX.toIsEmbedding.toHomeomorph_apply_coe x

/-- The inclusion `Vk (-2) → X` factors through the `Vk`-piece of the gluing. -/
lemma fU_comp_subtypeIncl (D : Work.Milnor.CapData) :
    fU D ≫ subtypeIncl (Work.Milnor.glueX D) (Work.Milnor.glueU D) = capPairMap D := by
  apply TopCat.ext
  intro x
  exact eU_apply_coe D x

/-- The unit sphere bundle `Mk (-2)` is carried into the cap `A` by `ιX`. -/
lemma capPairMap_mem (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) :
    ∀ x ∈ Set.range (Work.Milnor.mkToVkFun (-2)), D.ιX x ∈ Set.range D.ιY := by
  intro x hx
  obtain ⟨q, rfl⟩ := hx
  refine ⟨D.φ (Work.Milnor.mkToVkFun (-2) q), ?_⟩
  exact D.ιY_eq_ιX_iff.mpr ⟨by
    rw [hU]
    exact Work.Milnor.mem_collar.mpr (Work.Milnor.one_lt_fibreNorm_mkToVkFun (-2) q), rfl⟩

/-! ## The intermediate maps, with short names -/

/-- The relative cochain map induced by `ιX`. -/
abbrev capRelMap (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) :=
  relComplexMap (X₁ := TopCat.of (Submission.Milnor.Vk (-2))) (X₂ := Work.Milnor.glueX D) ℤ
    (Set.range (Work.Milnor.mkToVkFun (-2))) (Set.range D.ιY)
    (capPairMap D) (capPairMap_mem D hU)

/-- The relative restriction `H⁴(Vk(-2), Mk(-2)) → H⁴(Vk(-2))`. -/
abbrev vkRelRestr : relCohomology ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
      (Set.range (Work.Milnor.mkToVkFun (-2))) 4 ⟶
    singularCohomology ℤ 4 (TopCat.of (Submission.Milnor.Vk (-2))) :=
  HomologicalComplex.homologyMap (relIncl ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
    (Set.range (Work.Milnor.mkToVkFun (-2)))) 4

/-- The relative restriction `H⁴(X, A) → H⁴(X)`. -/
abbrev capRelRestr (D : Work.Milnor.CapData) :
    relCohomology ℤ (Work.Milnor.glueX D) (Set.range D.ιY) 4 ⟶
      singularCohomology ℤ 4 (Work.Milnor.glueX D) :=
  HomologicalComplex.homologyMap (relIncl ℤ (Work.Milnor.glueX D) (Set.range D.ιY)) 4

/-- The absolute restriction `H⁴(X) → H⁴(Vk(-2))`. -/
abbrev capAbsRestr (D : Work.Milnor.CapData) :
    singularCohomology ℤ 4 (Work.Milnor.glueX D) ⟶
      singularCohomology ℤ 4 (TopCat.of (Submission.Milnor.Vk (-2))) :=
  singularCohomologyMap ℤ (TopCat.of (Submission.Milnor.Vk (-2))) (Work.Milnor.glueX D)
    (capPairMap D) 4

/-- The relative restriction of the cochain map `ιX` to the absolute complexes, on `H⁴`. -/
lemma capRelMap_comp_relIncl (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) :
    HomologicalComplex.homologyMap (capRelMap D hU) 4 ≫ vkRelRestr
      = capRelRestr D ≫ capAbsRestr D := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ 4)
    (relComplexMap_comp_relIncl (R := ℤ) (Set.range (Work.Milnor.mkToVkFun (-2)))
      (Set.range D.ιY) (capPairMap D) (capPairMap_mem D hU))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact h

/-- The inclusion of the `Vk`-piece induces a surjection on `H⁴`. -/
lemma epi_singularCohomologyMap_subtypeIncl (D : Work.Milnor.CapData)
    (hU : D.U = Work.Milnor.collar (-2)) :
    Epi (singularCohomologyMap ℤ (TopCat.of ↥(Work.Milnor.glueU D)) (Work.Milnor.glueX D)
      (subtypeIncl (Work.Milnor.glueX D) (Work.Milnor.glueU D)) 4) := by
  rw [ModuleCat.epi_iff_surjective]
  have hcov : Work.Milnor.glueU D ∪ Work.Milnor.glueV D = Set.univ :=
    Work.Milnor.glueU_union_glueV D
  haveI hIso := CompatIso.isIso_smallIsoHom (Work.Milnor.glueU D) (Work.Milnor.glueV D)
    (Work.Milnor.isOpen_glueU D) (Work.Milnor.isOpen_glueV D) hcov 4
  have h2 : Function.Surjective (HomologicalComplex.homologyMap
      (mvCochainF (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4).hom :=
    (ModuleCat.epi_iff_surjective _).mp
      (Work.Milnor.mvCohF_epi (Work.Milnor.glueU D) (Work.Milnor.glueV D) 4
        (Work.Milnor.isZero_cochainUV D hU 4 (by norm_num) (by norm_num)))
  have h3 : Function.Surjective (HomologicalComplex.homologyMap
      (biprod.fst : cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D)
        ⊞ cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)
        ⟶ cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4).hom :=
    (ModuleCat.epi_iff_surjective _).mp
      (epi_homologyMap_biprod_fst (cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D))
        (cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4)
  have key : CompatIso.smallIsoHom (Work.Milnor.glueU D) (Work.Milnor.glueV D)
        (Work.Milnor.isOpen_glueU D) (Work.Milnor.isOpen_glueV D) hcov 4
      ≫ HomologicalComplex.homologyMap (mvCochainF (Work.Milnor.glueU D)
          (Work.Milnor.glueV D)) 4
      ≫ HomologicalComplex.homologyMap
          (biprod.fst : cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D)
            ⊞ cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)
            ⟶ cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4
      = singularCohomologyMap ℤ (TopCat.of ↥(Work.Milnor.glueU D)) (Work.Milnor.glueX D)
          (subtypeIncl (Work.Milnor.glueX D) (Work.Milnor.glueU D)) 4 := by
    have step : HomologicalComplex.homologyMap (mvCochainF (Work.Milnor.glueU D)
          (Work.Milnor.glueV D)) 4
        ≫ HomologicalComplex.homologyMap
            (biprod.fst : cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D)
              ⊞ cochainV (Work.Milnor.glueU D) (Work.Milnor.glueV D)
              ⟶ cochainU (Work.Milnor.glueU D) (Work.Milnor.glueV D)) 4
        = HomologicalComplex.homologyMap (dualComplexMap ℤ
            (singularChains ℤ (TopCat.of ↥(Work.Milnor.glueU D)))
            (smallChains (Work.Milnor.glueU D) (Work.Milnor.glueV D))
            (smallOfU (Work.Milnor.glueU D) (Work.Milnor.glueV D))) 4 := by
      rw [← HomologicalComplex.homologyMap_comp, mvCochainF_comp_fst]
    rw [step, CompatIso.smallIsoHom_comp_smallOfU (Work.Milnor.glueU D) (Work.Milnor.glueV D)
      (Work.Milnor.isOpen_glueU D) (Work.Milnor.isOpen_glueV D) hcov 4]
  rw [← key]
  exact surjective_comp _ _ (surjective_of_isIso _) (surjective_comp _ _ h2 h3)

/-- The absolute restriction `H⁴(X) → H⁴(Vk(-2))` is surjective. -/
lemma epi_capPairMap (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) :
    Epi (capAbsRestr D) := by
  rw [ModuleCat.epi_iff_surjective]
  have hfac : capPairMap D = fU D ≫ subtypeIncl (Work.Milnor.glueX D) (Work.Milnor.glueU D) :=
    fU_comp_subtypeIncl D
  haveI hIso := isIso_singularCohomologyMap_homeo (eU D) 4
  have h2 : Function.Surjective (singularCohomologyMap ℤ (TopCat.of ↥(Work.Milnor.glueU D))
      (Work.Milnor.glueX D)
      (subtypeIncl (Work.Milnor.glueX D) (Work.Milnor.glueU D)) 4).hom :=
    (ModuleCat.epi_iff_surjective _).mp (epi_singularCohomologyMap_subtypeIncl D hU)
  change Function.Surjective (singularCohomologyMap ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
    (Work.Milnor.glueX D) (capPairMap D) 4).hom
  rw [hfac, singularCohomologyMap_comp]
  exact surjective_comp _ _ h2 (surjective_of_isIso _)

/-! ## The cohomology of the two sub-pairs -/

/-- The cap `A = ιY '' ℝ⁸` has vanishing cohomology in positive degrees. -/
lemma subsingleton_range_ιY (D : Work.Milnor.CapData) (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton ↥(singularCohomology ℤ n (TopCat.of ↥(Set.range D.ιY))) := by
  haveI : ContractibleSpace ↥(Set.range D.ιY) :=
    (D.isOpenEmbedding_ιY.toIsEmbedding.toHomeomorph.symm).contractibleSpace
  have h := contractible ℤ (TopCat.of ↥(Set.range D.ιY)) (n - 1)
  rw [Nat.sub_add_cancel hn] at h
  exact ModuleCat.isZero_iff_subsingleton.mp h

/-- The sphere bundle `Mk (-2) ≃ S⁷` has vanishing cohomology except in degrees `0` and `7`. -/
lemma subsingleton_range_mkToVkFun (n : ℕ) (hn0 : n ≠ 0) (hn7 : n ≠ 7) :
    Subsingleton ↥(singularCohomology ℤ n
      (TopCat.of ↥(Set.range (Work.Milnor.mkToVkFun (-2))))) := by
  obtain ⟨h⟩ := Work.Milnor.mkToVkRangeHomeomorph (-2)
  obtain ⟨e1⟩ := cohomologyIso_of_homotopyEquiv h.toHomotopyEquiv n
  obtain ⟨e2⟩ := Work.Milnor.cohomology_Mk_minus_two n
  have hz : (if n = 0 then 1 else 0) + (if n = 7 then 1 else 0) = 0 := by
    rw [if_neg hn0, if_neg hn7, add_zero]
  rw [hz] at e2
  have h0 : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) := ModuleCat.isZero_of_subsingleton _
  exact ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso h0 (e1.symm ≪≫ e2))

/-! ## The relative restriction `H⁴(X,A) → H⁴(Vk(-2), Mk(-2))` is surjective -/

/-- The map of pairs `ιX` induces a surjection on the fourth relative cohomology. -/
lemma epi_capRelMap (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) :
    Epi (HomologicalComplex.homologyMap (capRelMap D hU) 4) := by
  rw [ModuleCat.epi_iff_surjective]
  haveI hβ : IsIso vkRelRestr :=
    pairIsoOfTrivial ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
      (Set.range (Work.Milnor.mkToVkFun (-2))) 3
      (subsingleton_range_mkToVkFun 3 (by norm_num) (by norm_num))
      (subsingleton_range_mkToVkFun 4 (by norm_num) (by norm_num))
  haveI hα : IsIso (capRelRestr D) :=
    pairIsoOfTrivial ℤ (Work.Milnor.glueX D) (Set.range D.ιY) 3
      (subsingleton_range_ιY D 3 (by norm_num))
      (subsingleton_range_ιY D 4 (by norm_num))
  have hψ : Function.Surjective (capAbsRestr D).hom :=
    (ModuleCat.epi_iff_surjective _).mp (epi_capPairMap D hU)
  -- `φ ≫ β = α ≫ ψ`, hence `φ` is surjective
  have hnat := capRelMap_comp_relIncl D hU
  intro y
  obtain ⟨z, hz⟩ := surjective_comp (capRelRestr D) (capAbsRestr D)
    (surjective_of_isIso (capRelRestr D)) hψ (vkRelRestr.hom y)
  refine ⟨z, injective_of_isIso vkRelRestr ?_⟩
  rw [← hz, ← ModuleCat.comp_apply, hnat, ModuleCat.comp_apply]

/-- **Naturality of the relative cup product along `ιX`**, for the capped pair. -/
lemma relCupHNatural_capPair (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2))
    (x y : relCohomology ℤ (Work.Milnor.glueX D) (Set.range D.ιY) 4) :
    HomologicalComplex.homologyMap (capRelMap D hU) 8
        (relCupH' ℤ (Work.Milnor.glueX D) (Set.range D.ιY) 4 4 x y)
      = relCupH' ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
          (Set.range (Work.Milnor.mkToVkFun (-2))) 4 4
          (HomologicalComplex.homologyMap (capRelMap D hU) 4 x)
          (HomologicalComplex.homologyMap (capRelMap D hU) 4 y) :=
  have hmem : ∀ x ∈ Set.range (Work.Milnor.mkToVkFun (-2)),
      (capPairMap D) x ∈ Set.range D.ιY := capPairMap_mem D hU
  relCupHNatural (X₁ := TopCat.of (Submission.Milnor.Vk (-2))) (X₂ := Work.Milnor.glueX D) ℤ
    (Set.range (Work.Milnor.mkToVkFun (-2))) (Set.range D.ιY) (capPairMap D) hmem 4 4 x y

end

end Work.Cohomology.Endgame.CappedTransfer
