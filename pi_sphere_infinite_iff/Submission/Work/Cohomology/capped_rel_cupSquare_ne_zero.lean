import Mathlib
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Cohomology.pairIsoOfTrivial
import Submission.Work.Cohomology.CompatIso.smallIsoHom
import Submission.Work.Cohomology.vk_relCup_ne_zero_of_relCapPair_ne_zero
import Submission.Work.Cohomology.Crux.vk_relCapPair_nonzero

/-!
# The cup square of the capped pair `(X, D⁸)` is non-degenerate

Let `F : Mk (-2) → S⁷` be a capping diffeomorphism and `D = cappedDatum F hF` the associated
gluing datum, so that `X = cappedSpace D` is the closed `8`-manifold `D(ξ) ∪_F D⁸` and
`A = Set.range D.ιY ⊆ X` is the cap.  Let `U = ιX '' Vk(-2)` be the `Vk`-piece of `X`.

This file proves that the relative cup product `⌣ : H⁴(X,A) × H⁴(X,A) → H⁸(X,A)` is not
identically zero: there is a nonzero class with nonzero square.

The argument transfers the corresponding statement for the disc-bundle pair
`(Vk (-2), Mk (-2))` (`Work.Cohomology.vk_cupSquare_ne_zero`) along the map of pairs
`ιX : (Vk (-2), Mk (-2)) → (X, A)`.  Since `relCupHNatural` says that the induced map is a ring
homomorphism for the relative cup product, it suffices to know that `ιX` induces a *surjection*
`H⁴(X,A) → H⁴(Vk(-2), Mk(-2))`.  By the pair long exact sequences (`pairIsoOfTrivial`) this
reduces to the surjectivity of the absolute restriction `H⁴(X) → H⁴(Vk(-2))`, which factors as

`H⁴(X) --(restrict to the small cochains)--> H⁴(C^{U,A}) --(mvCochainF)--> H⁴(U) ⊕ H⁴(A)
   --(projection)--> H⁴(U) --(homeomorphism)--> H⁴(Vk(-2))`.

Each stage is a surjection: the first is an isomorphism (`isIso_smallIsoHom`), the second has an
epimorphic first component in degree `4` (`Work.Milnor.mvCohF_epi` together with
`smallIsoHom_comp_smallOfU` and `mvCochainF_comp_fst`), the third is the projection of a
biproduct, and the last is induced by the homeomorphism `eU`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

open Work.Cohomology.CompatIso

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
  haveI hIso := isIso_smallIsoHom (Work.Milnor.glueU D) (Work.Milnor.glueV D)
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
  have key : smallIsoHom (Work.Milnor.glueU D) (Work.Milnor.glueV D)
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
    rw [step, smallIsoHom_comp_smallOfU (Work.Milnor.glueU D) (Work.Milnor.glueV D)
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

/-! ## The crux for the disc-bundle pair, in the form used below

The crux is available in two equivalent forms: `Work.Cohomology.vk_cupSquare_ne_zero` (the cup
square of the Thom class is nonzero) and the relative cap-product statement
`Work.Cohomology.Crux.vk_relCapPair_nonzero`, which the importable bridge
`Work.Cohomology.vk_relCup_ne_zero_of_relCapPair_ne_zero` turns into the cup-square form. -/

/-- The crux for the pair `(Vk (-2), Mk (-2))`, derived from the relative cap-product
non-vanishing `Work.Cohomology.Crux.vk_relCapPair_nonzero`. -/
lemma vk_cupSquare_of_relCapPair :
    ∃ u : relCohomology ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
        (Set.range (Work.Milnor.mkToVkFun (-2))) 4,
      u ≠ 0 ∧ relCupH' ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
        (Set.range (Work.Milnor.mkToVkFun (-2))) 4 4 u u ≠ 0 := by
  obtain ⟨u, c, hu, hcap⟩ := Work.Cohomology.Crux.vk_relCapPair_nonzero
  exact ⟨u, hu, vk_relCup_ne_zero_of_relCapPair_ne_zero u ⟨c, hcap⟩⟩

/-! ## The main theorem -/

/-- **The relative cup square of the capped pair is non-degenerate.** -/
lemma exists_relCupSquare (D : Work.Milnor.CapData) (hU : D.U = Work.Milnor.collar (-2)) :
    ∃ x : relCohomology ℤ (Work.Milnor.glueX D) (Set.range D.ιY) 4,
      x ≠ 0 ∧ relCupH' ℤ (Work.Milnor.glueX D) (Set.range D.ιY) 4 4 x x ≠ 0 := by
  obtain ⟨u, hu, huu⟩ := vk_cupSquare_of_relCapPair
  haveI hφ : Epi (HomologicalComplex.homologyMap (capRelMap D hU) 4) := epi_capRelMap D hU
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap (capRelMap D hU) 4).hom :=
    (ModuleCat.epi_iff_surjective _).mp hφ
  obtain ⟨x, hx⟩ := hsurj u
  refine ⟨x, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at hx
    exact hu hx.symm
  · intro hxx
    have hcup := relCupHNatural_capPair D hU x x
    rw [hx, hxx] at hcup
    simp only [map_zero] at hcup
    exact huu hcup.symm

theorem capped_rel_cupSquare_ne_zero
    (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8) (hF : Work.Milnor.IsCappingDiffeo F) :
    ∃ x : Work.Cohomology.relCohomology ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
        (Set.range (Work.Milnor.cappedDatum F hF).ιY) 4,
      x ≠ 0 ∧ Work.Cohomology.relCupH' ℤ
        (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
        (Set.range (Work.Milnor.cappedDatum F hF).ιY) 4 4 x x ≠ 0 := by
  simpa only [Work.Milnor.glueX, Work.Milnor.cappedSpace] using
    exists_relCupSquare (Work.Milnor.cappedDatum F hF) (Work.Milnor.cappedDatum_U F hF)

end

end Work.Cohomology
