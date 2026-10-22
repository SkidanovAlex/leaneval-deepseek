/-
Copyright (c) 2026 The CWIND team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.GClass.SigmaFst

/-!
# CWIND/GClass — the simplices of a disjoint union

The compact-open mapping space out of the standard simplex into a disjoint union of spaces is the
disjoint union of the mapping spaces:

`(⊔_j X_j)^{Δⁿ} ≅ ⊔_j X_j^{Δⁿ}`.

This is the topological input of `G_sigma` (CW complexes are closed under disjoint unions).

## Proof outline

Write `σ_j : X_j ⟶ ⊔_j X_j` for the `j`-th coprojection.  The map in question is
`Φ : ⊔_j X_j^{Δⁿ} ⟶ (⊔_j X_j)^{Δⁿ}`, `(j, g) ↦ σ_j ∘ g`.  Since `Δⁿ` is compact, path connected
and nonempty (`SimplexCategory.toTop₀`), a continuous map `f : Δⁿ ⟶ ⊔_j X_j` has image inside a
single summand: `Work.CWIND.GClass.singSpace_sigmaFst_eq_eq`.  Consequently

* `Φ` is injective (evaluate at a point of `Δⁿ` and use injectivity of `σ_j`), and surjective
  (corestrict `f` to its summand, `Work.CWIND.GClass.corestrict`);
* `Φ` is an open map: an open subset of `X_j^{Δⁿ}` is a union of finite intersections of
  compact-open subbasic sets `N(K, W)`, and
  `σ_j '' N(K, W) = {f : Δⁿ ⟶ ⊔_j X_j | range f ⊆ range σ_j} ∩ N(K, σ_j '' W)`,
  both factors being open (the first because `Δⁿ` is compact, the second by definition of the
  compact-open topology and openness of `σ_j`).

So `Φ` is a bijective open map, hence a homeomorphism, hence an isomorphism in `TopCat`
(`TopCat.isIso_of_bijective_of_isOpenMap`).  The statement of `SigmaCodHomeo` is obtained by
transporting this along the canonical isomorphism `∐_j X_j^{Δⁿ} ≅ ⊔_j X_j^{Δⁿ}`
(`TopCat.sigmaIsoSigma`).

## Main results

* `Work.CWIND.GClass.sigmaPostcompHom` — the explicit map `⊔_j X_j^{Δⁿ} ⟶ (⊔_j X_j)^{Δⁿ}`.
* `Work.CWIND.GClass.SigmaCodHomeo` — `⊔_j X_j^{Δⁿ} → (⊔_j X_j)^{Δⁿ}` is an isomorphism in
  `TopCat`.
-/

noncomputable section

open CategoryTheory Limits

namespace Work.CWIND.GClass

variable {J : Type} (X : J → TopCat.{0}) (n : ℕ)

/-- The `j`-th piece of the source, `X_j^{Δⁿ}`. -/
abbrev sgPiece (j : J) : TopCat.{0} := Work.CWIND.singSpace (X j) n

/-- The target, `(⊔_j X_j)^{Δⁿ}`. -/
abbrev sgTot : TopCat.{0} := Work.CWIND.singSpace (TopCat.of (Σ j, (X j : Type))) n

/-- A point of the simplex (which is nonempty). -/
def simplexPt : ↥(Work.CWIND.Δ n) := Classical.arbitrary _

/-- The set of maps `Δⁿ ⟶ ⊔_j X_j` whose image lies in the `j`-th summand. -/
abbrev sigmaFiber (j : J) : Set ↥(sgTot X n) := {f | ∀ t, (f t).1 = j}

/-- Corestriction of a map with image in the `j`-th summand to that summand. -/
abbrev sigmaFiberRestrict (j : J) : ↥(sigmaFiber X n j) → ↥(sgPiece X n j) :=
  fun F => corestrict n F.1 j F.2

/-- The explicit map `⊔_j X_j^{Δⁿ} ⟶ (⊔_j X_j)^{Δⁿ}`, `(j, g) ↦ σ_j ∘ g`. -/
def sigmaPostcompHom : TopCat.of ((j : J) × ↥(sgPiece X n j)) ⟶ sgTot X n :=
  TopCat.ofHom ⟨fun p => (Work.CWIND.singSpacePostcomp (TopCat.sigmaι X p.1) n).hom p.2, by
    refine continuous_sigma_iff.2 fun j => ?_
    exact ContinuousMap.continuous_postcomp (TopCat.sigmaι X j).hom⟩

@[simp]
lemma sigmaPostcompHom_apply (j : J) (g : ↥(sgPiece X n j)) :
    ⇑(sigmaPostcompHom X n) ⟨j, g⟩ = (TopCat.sigmaι X j).hom.comp g := rfl

lemma sigmaPostcompHom_apply_apply (j : J) (g : ↥(sgPiece X n j)) (t : ↥(Work.CWIND.Δ n)) :
    ⇑(sigmaPostcompHom X n) ⟨j, g⟩ t = Sigma.mk j (g t) := by
  rw [sigmaPostcompHom_apply, ContinuousMap.comp_apply, sigmaι_apply]

/-- Injectivity of `⟨j, ·⟩` (a fixed fibre of the disjoint union). -/
lemma sigmaMk_inj {J : Type} {X : J → TopCat.{0}} (j : J) {a b : ↥(X j)}
    (h : (⟨j, a⟩ : Sigma fun i => (X i : Type)) = ⟨j, b⟩) : a = b :=
  (heq_eq_eq _ _).mp (Sigma.mk.inj_iff.mp h).2

/-- The set of maps `Δⁿ ⟶ ⊔_j X_j` with image in the `j`-th summand is open: it is
`{f | range f ⊆ range (σ_j)}` and `Δⁿ` is compact. -/
lemma isOpen_sigmaFiber (j : J) : IsOpen (sigmaFiber X n j) := by
  have : CompactSpace ↥(Work.CWIND.Δ n) := by
    rw [Work.CWIND.Δ, SimplexCategory.toTop₀_obj]; infer_instance
  have hmem : ∀ (f : C(Work.CWIND.Δ n, TopCat.of (Σ j, (X j : Type))))
      (t : ↥(Work.CWIND.Δ n)), (f t ∈ Set.range (fun x : ↥(X j) => (⟨j, x⟩ :
        Sigma fun i => (X i : Type)))) ↔ (f t).1 = j := by
    intro f t; constructor
    · rintro ⟨y, hy⟩
      rw [← hy]
    · intro h
      exact ⟨h ▸ (f t).2, sigmaMk_cast (f t) j h⟩
  have hset : sigmaFiber X n j
      = {f : C(Work.CWIND.Δ n, TopCat.of (Σ j, (X j : Type))) |
          Set.range ⇑f ⊆ Set.range (fun x : ↥(X j) => (⟨j, x⟩ :
            Sigma fun i => (X i : Type)))} := by
    ext f
    simp only [sigmaFiber, Set.mem_ofPred_eq, Set.range_subset_iff]
    exact ⟨fun h t => (hmem f t).mpr (h t), fun h t => (hmem f t).mp (h t)⟩
  rw [hset]
  exact ContinuousMap.isOpen_setOfPred_range_subset (isOpen_range_sigmaMk (i := j))

/-- Corestriction to the `j`-th summand is continuous on the maps with image in that summand. -/
lemma continuous_sigmaFiberRestrict (j : J) : Continuous (sigmaFiberRestrict X n j) := by
  rw [ContinuousMap.continuous_compactOpen]
  intro K hK W hW
  have hset : {F : ↥(sigmaFiber X n j) | Set.MapsTo (sigmaFiberRestrict X n j F) K W}
      = Subtype.val ⁻¹'
        {f : C(Work.CWIND.Δ n, TopCat.of (Σ j, (X j : Type))) |
          Set.MapsTo f K ((fun x : ↥(X j) => (⟨j, x⟩ : Sigma fun i => (X i : Type))) '' W)} := by
    ext F; constructor
    · intro h t ht
      refine ⟨sigmaFiberRestrict X n j F t, h ht, ?_⟩
      show Sigma.mk j (corestrict n F.1 j F.2 t) = F.1 t
      exact congrFun (congrArg DFunLike.coe (sigmaι_corestrict n F.1 j F.2)) t
    · intro h t ht
      obtain ⟨w, hw, hw'⟩ := h ht
      have h1 : (⟨j, sigmaFiberRestrict X n j F t⟩ : Sigma fun i => (X i : Type))
          = ⟨j, w⟩ :=
        (congrFun (congrArg DFunLike.coe (sigmaι_corestrict n F.1 j F.2)) t).trans hw'.symm
      rw [sigmaMk_inj j h1]
      exact hw
  rw [hset]
  have hWopen : IsOpen ((fun x : ↥(X j) => (⟨j, x⟩ : Sigma fun i => (X i : Type))) '' W) :=
    isOpenMap_sigmaMk (σ := fun i => (X i : Type)) (i := j) W hW
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hK hWopen).preimage continuous_subtype_val

/-- The image of an open subset of an open subspace is open in the ambient space. -/
lemma isOpen_subtype_val_image {Z : Type*} [TopologicalSpace Z] {V : Set Z} (hV : IsOpen V)
    {U : Set V} (hU : IsOpen U) : IsOpen ((Subtype.val : V → Z) '' U) := by
  obtain ⟨T, hT, hUT⟩ := isOpen_induced_iff.mp hU
  have h2 : (Subtype.val : V → Z) '' U = V ∩ T := by
    rw [← hUT]
    exact Subtype.image_preimage_coe V T
  rw [h2]
  exact hV.inter hT

/-- The corestriction of `σ_j ∘ g` to the `j`-th summand is `g`. -/
lemma corestrict_sigmaPostcompHom (j : J) (g : ↥(sgPiece X n j))
    (h : ∀ t, (⇑(sigmaPostcompHom X n) ⟨j, g⟩ t).1 = j) :
    corestrict n (⇑(sigmaPostcompHom X n) ⟨j, g⟩) j h = g := by
  refine ContinuousMap.ext fun t => sigmaMk_inj j ?_
  calc (⟨j, corestrict n (⇑(sigmaPostcompHom X n) ⟨j, g⟩) j h t⟩ : Sigma fun i => (X i : Type))
      = ⇑(sigmaPostcompHom X n) ⟨j, g⟩ t :=
        congrFun (congrArg DFunLike.coe (sigmaι_corestrict n _ j h)) t
    _ = (⟨j, g t⟩ : Sigma fun i => (X i : Type)) := sigmaPostcompHom_apply_apply X n j g t

lemma sigmaPostcompHom_injective : Function.Injective ⇑(sigmaPostcompHom X n) := by
  rintro ⟨j, g⟩ ⟨k, g'⟩ h
  have h1 : ⇑(sigmaPostcompHom X n) ⟨j, g⟩ (simplexPt n) =
      ⇑(sigmaPostcompHom X n) ⟨k, g'⟩ (simplexPt n) := by
    rw [h]
  rw [sigmaPostcompHom_apply_apply, sigmaPostcompHom_apply_apply] at h1
  have hjk : j = k := (Sigma.mk.inj_iff.mp h1).1
  subst hjk
  have hgg : g = g' := by
    refine ContinuousMap.ext fun t => sigmaMk_inj j ?_
    have h2 : ⇑(sigmaPostcompHom X n) ⟨j, g⟩ t = ⇑(sigmaPostcompHom X n) ⟨j, g'⟩ t := by rw [h]
    rw [sigmaPostcompHom_apply_apply, sigmaPostcompHom_apply_apply] at h2
    exact h2
  rw [hgg]

/-- Every map `Δⁿ ⟶ ⊔_j X_j` is `σ_j ∘ g` for some `j` and some `g : Δⁿ ⟶ X_j`. -/
lemma sigmaPostcompHom_surjective : Function.Surjective ⇑(sigmaPostcompHom X n) := by
  intro f
  refine ⟨⟨(f (simplexPt n)).1, corestrict n f (f (simplexPt n)).1 (fun t => ?_)⟩, ?_⟩
  · exact singSpace_sigmaFst_eq_eq X n f t (simplexPt n)
  · rw [sigmaPostcompHom_apply]
    exact sigmaι_corestrict n f _ _

lemma isOpenMap_sigmaPostcompHom : IsOpenMap ⇑(sigmaPostcompHom X n) := by
  refine isOpenMap_sigma.mpr fun j => ?_
  intro U hU
  have hset : (fun g : ↥(sgPiece X n j) => ⇑(sigmaPostcompHom X n) ⟨j, g⟩) '' U
      = Subtype.val '' (sigmaFiberRestrict X n j ⁻¹' U) := by
    ext f; constructor
    · rintro ⟨g, hgU, rfl⟩
      have hf : ∀ t, (⇑(sigmaPostcompHom X n) ⟨j, g⟩ t).1 = j := by
        intro t; rw [sigmaPostcompHom_apply_apply]
      refine ⟨⟨⇑(sigmaPostcompHom X n) ⟨j, g⟩, hf⟩, ?_, rfl⟩
      show sigmaFiberRestrict X n j ⟨⇑(sigmaPostcompHom X n) ⟨j, g⟩, hf⟩ ∈ U
      rw [show sigmaFiberRestrict X n j ⟨⇑(sigmaPostcompHom X n) ⟨j, g⟩, hf⟩ = g from
        corestrict_sigmaPostcompHom X n j g hf]
      exact hgU
    · rintro ⟨F, hFU, rfl⟩
      refine ⟨sigmaFiberRestrict X n j F, hFU, ?_⟩
      show ⇑(sigmaPostcompHom X n) ⟨j, sigmaFiberRestrict X n j F⟩ = ↑F
      rw [sigmaPostcompHom_apply]
      exact sigmaι_corestrict n F.1 j F.2
  rw [hset]
  exact isOpen_subtype_val_image (isOpen_sigmaFiber X n j)
    ((continuous_sigmaFiberRestrict X n j).isOpen_preimage U hU)

/-- The explicit map is an isomorphism in `TopCat`. -/
lemma isIso_sigmaPostcompHom : IsIso (sigmaPostcompHom X n) :=
  TopCat.isIso_of_bijective_of_isOpenMap _ ⟨sigmaPostcompHom_injective X n,
    sigmaPostcompHom_surjective X n⟩ (isOpenMap_sigmaPostcompHom X n)

/-- The `j`-th coprojection of the explicit disjoint union is `σ_j ∘ ·`. -/
lemma sigmaι_comp_sigmaPostcompHom (j : J) :
    TopCat.sigmaι (fun j => sgPiece X n j) j ≫ sigmaPostcompHom X n
      = Work.CWIND.singSpacePostcomp (TopCat.sigmaι X j) n := by
  apply TopCat.ext
  intro g
  show ⇑(sigmaPostcompHom X n) ⟨j, g⟩ = ⇑(Work.CWIND.singSpacePostcomp (TopCat.sigmaι X j) n) g
  rw [sigmaPostcompHom_apply, Work.CWIND.singSpacePostcomp_apply]

/-- **The simplices of a disjoint union.**  For a family of spaces `X : J → TopCat` the canonical
map `⊔_j X_j^{Δⁿ} ⟶ (⊔_j X_j)^{Δⁿ}` induced by the coprojections is an isomorphism in `TopCat`;
equivalently, the compact-open mapping space out of the simplex into a disjoint union is the
disjoint union of the mapping spaces. -/
theorem SigmaCodHomeo {J : Type} (X : J → TopCat.{0}) (n : ℕ) :
    CategoryTheory.IsIso (CategoryTheory.Limits.Sigma.desc
      (fun j => Work.CWIND.singSpacePostcomp (TopCat.sigmaι X j) n)) := by
  have hφ : CategoryTheory.Limits.Sigma.desc
      (fun j => Work.CWIND.singSpacePostcomp (TopCat.sigmaι X j) n)
      = (TopCat.sigmaIsoSigma (fun j => sgPiece X n j)).hom ≫ sigmaPostcompHom X n := by
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, TopCat.sigmaIsoSigma_hom_ι, Sigma.ι_comp_desc]
    exact (sigmaι_comp_sigmaPostcompHom X n j).symm
  rw [hφ]
  exact (isIso_comp_left_iff _ _).mpr (isIso_sigmaPostcompHom X n)

end Work.CWIND.GClass
