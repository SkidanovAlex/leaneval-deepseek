import Mathlib
import Submission.Work.Cohomology.StageSplitDefs
import Submission.Work.Cohomology.StageSplitTransport
import Submission.Work.Cohomology.localClass_union_injective
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.isZero_dualComplex_empty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `N = 1` case of the transport of a stage splitting

For `N ≥ 2` the connecting map `δ : H_N(ℝ^N, ℝ^N ∖ T) → H_{N-1}(ℝ^N ∖ T)` of the pair is an
isomorphism, and a left inverse of the stage map `lkMap` transports to a left inverse of the map
`complMap` on the complements (`Work.Cohomology.stage_split_of_lkMap_ge_two`).  For `N = 1` the
connecting map is *not* an isomorphism: it identifies `LK 1 K = H₁(ℝ, ℝ∖K)` with the kernel of the
augmentation `ε_K : H₀(ℝ∖K) → ℤ`.  The present file carries out the transport in this case.

The argument: `δ_K` is injective with image `ker ε_K`, so it exhibits `LK 1 K ≃ ker ε_K`
(`eK`), and under these identifications `lkMap` becomes the restriction of `complMap` to the
kernels (`projKer_complMap`).  A left inverse `sL` of `lkMap` therefore gives a left inverse `σ`
of `complMap` *on the kernels of the augmentations*.  Choosing a point `x₀ ∈ Tᶜ` we have a section
`κ_T : ℤ → H₀(Tᶜ)` of `ε_T` (`aug_kappa`) and hence the decomposition
`H₀(Kᶜ) ≅ ker ε_K ⊕ ℤ`; with `κ_S := complMap ∘ κ_T` the map `s := σ ∘ (id - κ_S ε_S) + κ_T ε_S`
is a left inverse of `complMap` (`stageSection_spec`).  The remaining case `Tᶜ = ∅` (where both
complements are empty and `H₀` vanishes) is trivial.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

-- Prefer the `Submodule`-derived `ℤ`-module structure on subtypes throughout, so that the various
-- spellings (kernels, ranges, `AddCommGroup.toIntModule`) agree definitionally.
attribute [local instance 10000] Submodule.module

/-- The real line `ℝ¹ = ℝ` used as the ambient space. -/
abbrev Line : Type := EuclideanSpace ℝ (Fin 1)

/-- The degree-`0` singular homology of the complement of `K`. -/
abbrev VC (K : Set Line) : Type :=
  ↥((singularChains ℤ (TopCat.of (Set.compl K))).homology 0)

/-- The identification of `H₀(Kᶜ)` with the coproduct of copies of `ℤ` indexed by the path
components of `Kᶜ`. -/
noncomputable def h0iso (K : Set Line) :
    ((singularChains ℤ (TopCat.of (Set.compl K))).homology 0) ≅
      ∐ (fun _ : ZerothHomotopy (TopCat.of (Set.compl K)) ↦ ModuleCat.of ℤ ℤ) :=
  TopCat.singularHomology₀Iso (TopCat.of (Set.compl K)) (ModuleCat.of ℤ ℤ)

/-- The augmentation `H₀(Kᶜ) → ℤ`, in the spelling compatible with `h0iso`. -/
noncomputable def epsC (K : Set Line) :
    ((singularChains ℤ (TopCat.of (Set.compl K))).homology 0) ⟶ (ModuleCat.of ℤ ℤ) :=
  (h0iso K).hom ≫
    Sigma.desc (fun _ : ZerothHomotopy (TopCat.of (Set.compl K)) ↦ 𝟙 (ModuleCat.of ℤ ℤ))

/-- The augmentation `ε_K : H₀(Kᶜ) → ℤ` as a linear map. -/
noncomputable def augK (K : Set Line) : VC K →ₗ[ℤ] ℤ := (epsC K).hom

/-- `augK` is Mathlib's singular augmentation. -/
lemma augK_eq_eps (K : Set Line) :
    augK K = (TopCat.singularHomology₀ε (TopCat.of (Set.compl K)) (ModuleCat.of ℤ ℤ)).hom := by
  rw [augK, epsC]
  exact congrArg ModuleCat.Hom.hom
    (TopCat.singularHomology₀Iso_sigma_desc_id (TopCat.of (Set.compl K)) (ModuleCat.of ℤ ℤ))

/-- The connecting map `δ_K : H₁(ℝ, ℝ∖K) → H₀(ℝ∖K)` of the pair `(ℝ, ℝ∖K)`, restricted to degree
`0`. -/
noncomputable def deltaK (K : Set Line) : LK 1 K →ₗ[ℤ] VC K :=
  (hPairδ (TopCat.of Line) (Set.compl K) 0).hom

/-- A point of `Kᶜ` gives a section `ℤ → H₀(Kᶜ)` of the augmentation. -/
noncomputable def kappaMor (K : Set Line) (x₀ : ↥(Set.compl K)) :
    (ModuleCat.of ℤ ℤ) ⟶ ((singularChains ℤ (TopCat.of (Set.compl K))).homology 0) :=
  Sigma.ι (fun _ : ZerothHomotopy (TopCat.of (Set.compl K)) ↦ ModuleCat.of ℤ ℤ)
    (ZerothHomotopy.mk x₀) ≫ (h0iso K).inv

/-- The section `κ_K : ℤ → H₀(Kᶜ)` of the augmentation determined by a point of `Kᶜ`. -/
noncomputable def kappa (K : Set Line) (x₀ : ↥(Set.compl K)) : ℤ →ₗ[ℤ] VC K :=
  (kappaMor K x₀).hom

/-- `ε_K ∘ κ_K = id`. -/
lemma augK_kappa (K : Set Line) (x₀ : ↥(Set.compl K)) :
    augK K ∘ₗ kappa K x₀ = LinearMap.id := by
  have h1 : kappaMor K x₀ ≫ epsC K = 𝟙 (ModuleCat.of ℤ ℤ) := by
    rw [kappaMor, epsC]
    simp only [Category.assoc]
    rw [← Category.assoc (f := (h0iso K).inv), Iso.inv_hom_id (h0iso K), Category.id_comp,
      Sigma.ι_desc]
  rw [augK, kappa]
  rw [← ModuleCat.hom_comp, h1, ModuleCat.hom_id]

/-- The connecting map `δ_K` is injective (as `H₁(ℝ) = 0`). -/
lemma deltaK_injective (K : Set Line) : Function.Injective (deltaK K) := by
  have h1 : IsZero ((singularChains ℤ (TopCat.of Line)).homology 1) :=
    homologyContractible 1 (by norm_num)
  have hf : (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π (inclChains (TopCat.of Line) (Set.compl K))) 1)
      (hPairδ (TopCat.of Line) (Set.compl K) 0)
      (hPair_comp_δ (TopCat.of Line) (Set.compl K) 0)).f = 0 := h1.eq_of_src _ 0
  have hmono : Mono (hPairδ (TopCat.of Line) (Set.compl K) 0) :=
    (ShortComplex.exact_iff_mono _ hf).1 (hPair_exact₃ (TopCat.of Line) (Set.compl K) 0)
  exact (ModuleCat.mono_iff_injective _).mp hmono

/-- The image of `δ_K` is the kernel of the augmentation. -/
lemma deltaK_range (K : Set Line) : (deltaK K).range = (augK K).ker := by
  have hrange : (deltaK K).range =
      (HomologicalComplex.homologyMap (inclChains (TopCat.of Line) (Set.compl K)) 0).hom.ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hPair_exact₁ (TopCat.of Line) (Set.compl K) 0)
  rw [hrange, augK_eq_eps K]
  have hnat := epsilonNaturality (TopCat.of (Set.compl K)) (TopCat.of Line)
    (subtypeIncl (TopCat.of Line) (Set.compl K))
  have hnat' := congrArg ModuleCat.Hom.hom hnat
  rw [ModuleCat.hom_comp] at hnat'
  haveI : IsIso (TopCat.singularHomology₀ε (TopCat.of Line) (ModuleCat.of ℤ ℤ)) := inferInstance
  have hinj : Function.Injective
      (TopCat.singularHomology₀ε (TopCat.of Line) (ModuleCat.of ℤ ℤ)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hker : (TopCat.singularHomology₀ε (TopCat.of Line) (ModuleCat.of ℤ ℤ)).hom.ker = ⊥ :=
    LinearMap.ker_eq_bot_of_injective hinj
  rw [← hnat']
  rw [LinearMap.ker_comp_of_ker_eq_bot _ hker]

/-- The connecting map exhibits `LK 1 K` as the range of `δ_K`. -/
noncomputable def eK (K : Set Line) := LinearEquiv.ofInjective (deltaK K) (deltaK_injective K)

/-- The underlying value of `eK`. -/
lemma eK_apply (K : Set Line) (x : LK 1 K) : ↑(eK K x) = deltaK K x := rfl

/-- The inverse of `eK` on the underlying values. -/
lemma eK_symm_apply (K : Set Line) (y : (deltaK K).range) : deltaK K ((eK K).symm y) = ↑y := by
  rw [← eK_apply K ((eK K).symm y), LinearEquiv.apply_symm_apply]

/-- **The naturality square** in the form used here: `complMap ∘ δ_T = δ_S ∘ lkMap`. -/
lemma deltaK_nat {T S : Set Line} (h : S ⊆ T) :
    (complMap T S h).comp (deltaK T) = (deltaK S).comp (lkMap (N := 1) h) := by
  have hsq := lkMap_complMap_square (N := 1) h
  have hproof : (Set.compl_subset_compl.mpr h : Set.compl T ⊆ Set.compl S) =
      (fun y hy hyS => hy (h hyS)) := by
    funext y hy hyS; exact Subsingleton.elim _ _
  rw [hproof] at hsq
  simp only [deltaK, lkMap_eq_relCokerMap]
  exact hsq

/-- **Naturality of the augmentation**: `ε_S ∘ complMap = ε_T`. -/
lemma augK_complMap {T S : Set Line} (h : S ⊆ T) :
    (augK S).comp (complMap T S h) = augK T := by
  rw [augK_eq_eps S, augK_eq_eps T]
  rw [show complMap T S h = (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (Set.compl T))
    (TopCat.of (Set.compl S)) (inclSet (X := TopCat.of Line) (A := Set.compl T)
      (B := Set.compl S) (Set.compl_subset_compl.mpr h))) 0).hom from rfl]
  have hnat := epsilonNaturality (TopCat.of (Set.compl T)) (TopCat.of (Set.compl S))
    (inclSet (X := TopCat.of Line) (A := Set.compl T) (B := Set.compl S)
      (Set.compl_subset_compl.mpr h))
  have h2 := congrArg ModuleCat.Hom.hom hnat
  rw [ModuleCat.hom_comp] at h2
  exact h2

/-- The projection of `H₀(Kᶜ)` onto the kernel of the augmentation, using the decomposition
determined by the section `κ_K`. -/
noncomputable def projKer {T S : Set Line} (h : S ⊆ T) (x₀ : ↥(Set.compl T)) :=
  (LinearMap.id - ((complMap T S h).comp (kappa T x₀)).comp (augK S)).codRestrict
    (deltaK S).range (fun b => by
      have hκ : (augK S) ((complMap T S h) (kappa T x₀ (augK S b))) = augK S b := by
        have h1 : (augK S).comp ((complMap T S h).comp (kappa T x₀)) = LinearMap.id := by
          rw [← LinearMap.comp_assoc (f := kappa T x₀) (g := complMap T S h) (h := augK S),
            augK_complMap h, augK_kappa]
        have h2 := LinearMap.congr_fun h1 (augK S b)
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h2
      rw [deltaK_range S, LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
      rw [hκ, sub_self])

/-- **The key computation**: the projection onto the kernel intertwines `complMap` with `lkMap`. -/
lemma projKer_complMap {T S : Set Line} (h : S ⊆ T) (x₀ : ↥(Set.compl T)) (a : VC T)
    (hmem : augK T (a - kappa T x₀ (augK T a)) = 0) :
    projKer h x₀ (complMap T S h a) = eK S (lkMap (N := 1) h ((eK T).symm
      ⟨a - kappa T x₀ (augK T a), by
        rw [deltaK_range T, LinearMap.mem_ker]; exact hmem⟩)) := by
  have haug : (augK S) ((complMap T S h) a) = (augK T) a := by
    have h2 := LinearMap.congr_fun (augK_complMap h) a
    simpa only [LinearMap.comp_apply] using h2
  have hnat : (complMap T S h) (deltaK T ((eK T).symm ⟨a - kappa T x₀ (augK T a), by
        rw [deltaK_range T, LinearMap.mem_ker]; exact hmem⟩))
      = deltaK S (lkMap (N := 1) h ((eK T).symm ⟨a - kappa T x₀ (augK T a), by
        rw [deltaK_range T, LinearMap.mem_ker]; exact hmem⟩)) := by
    have h2 := LinearMap.congr_fun (deltaK_nat h) ((eK T).symm
      ⟨a - kappa T x₀ (augK T a), by
        rw [deltaK_range T, LinearMap.mem_ker]; exact hmem⟩)
    simpa only [LinearMap.comp_apply] using h2
  apply Subtype.ext
  show (complMap T S h) a - (complMap T S h) (kappa T x₀ (augK S ((complMap T S h) a)))
    = deltaK S (lkMap (N := 1) h ((eK T).symm
        ⟨a - kappa T x₀ (augK T a), by
          rw [deltaK_range T, LinearMap.mem_ker]; exact hmem⟩))
  rw [haug, ← map_sub, ← hnat, eK_symm_apply]

/-- The section of `complMap` constructed from a left inverse of `lkMap` (when `Tᶜ ≠ ∅`). -/
noncomputable def stageSection {T S : Set Line} (h : S ⊆ T) (x₀ : ↥(Set.compl T))
    (sL : LK 1 S →ₗ[ℤ] LK 1 T) : VC S →ₗ[ℤ] VC T :=
  (deltaK T).comp (sL.comp ((eK S).symm.toLinearMap.comp (projKer h x₀)))
    + (kappa T x₀).comp (augK S)

/-- **The section is a left inverse of `complMap`.** -/
lemma stageSection_spec {T S : Set Line} (h : S ⊆ T) (x₀ : ↥(Set.compl T))
    (sL : LK 1 S →ₗ[ℤ] LK 1 T) (hsL : sL.comp (lkMap (N := 1) h) = LinearMap.id) :
    (stageSection h x₀ sL).comp (complMap T S h) = LinearMap.id := by
  ext a
  have hsL' : ∀ y, sL (lkMap (N := 1) h y) = y := fun y => by
    have hh := LinearMap.congr_fun hsL y
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hh
  have hmem' : augK T (a - kappa T x₀ (augK T a)) = 0 := by
    rw [map_sub]
    have h2 : augK T (kappa T x₀ (augK T a)) = augK T a := by
      have h3 := LinearMap.congr_fun (augK_kappa T x₀) (augK T a)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h3
    rw [h2, sub_self]
  have haug : (augK S) ((complMap T S h) a) = (augK T) a := by
    have h2 := LinearMap.congr_fun (augK_complMap h) a
    simpa only [LinearMap.comp_apply] using h2
  simp only [stageSection, LinearMap.add_apply, LinearMap.comp_apply]
  rw [projKer_complMap h x₀ a hmem']
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply (eK S) _]
  rw [hsL' _]
  rw [eK_symm_apply]
  rw [haug]
  show a - kappa T x₀ (augK T a) + kappa T x₀ (augK T a) = a
  rw [sub_add_cancel]

/-- `H₀` of the empty space vanishes. -/
lemma isZero_VC_empty : IsZero ((singularChains ℤ (TopCat.of (∅ : Set Line))).homology 0) := by
  haveI : IsEmpty (ZerothHomotopy (TopCat.of (∅ : Set Line))) :=
    ⟨fun z => by
      obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
      exact x.2⟩
  have h : IsZero (∐ (fun _ : ZerothHomotopy (TopCat.of (∅ : Set Line)) ↦
      ModuleCat.of ℤ ℤ)) := isZero_coproduct_of_isEmpty _
  have e : ((singularChains ℤ (TopCat.of (∅ : Set Line))).homology 0) ≅
      ∐ (fun _ : ZerothHomotopy (TopCat.of (∅ : Set Line)) ↦ ModuleCat.of ℤ ℤ) :=
    TopCat.singularHomology₀Iso (TopCat.of (∅ : Set Line)) (ModuleCat.of ℤ ℤ)
  exact IsZero.of_iso h e

theorem stage_split_of_lkMap_one {T S : Set (EuclideanSpace ℝ (Fin 1))}
    (h : S ⊆ T) (hL : ∃ s : Work.Cohomology.LK 1 S →ₗ[ℤ] Work.Cohomology.LK 1 T,
      s.comp (Work.Cohomology.lkMap (N := 1) h) = LinearMap.id) :
    ∃ s : ↥((Work.Cohomology.singularChains ℤ (TopCat.of (Set.compl S))).homology 0) →ₗ[ℤ]
        ↥((Work.Cohomology.singularChains ℤ (TopCat.of (Set.compl T))).homology 0),
      s.comp (Work.Cohomology.complMap T S h) = LinearMap.id := by
  obtain ⟨sL, hsL⟩ := hL
  by_cases hne : (Set.compl T).Nonempty
  · exact ⟨stageSection h ⟨hne.some, hne.some_mem⟩ sL,
      stageSection_spec h ⟨hne.some, hne.some_mem⟩ sL hsL⟩
  · have hT : (Set.compl T : Set Line) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    haveI : Subsingleton ↥((singularChains ℤ (TopCat.of (Set.compl T))).homology 0) := by
      rw [hT]
      exact ModuleCat.subsingleton_of_isZero isZero_VC_empty
    refine ⟨0, ?_⟩
    ext x
    exact Subsingleton.elim _ _

end

end Work.Cohomology
