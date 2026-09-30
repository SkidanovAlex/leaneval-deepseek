/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The piece cover of `(X/Γ) ⊗ Y` is locally directed (area SY, `relQuot`)

For a quotient datum `D` of an action of a finite group `Γ` on a `K`-scheme `X` and a `K`-scheme
`Y`, the relative quotient `(X/Γ) ⊗ Y` is covered by the *pieces* `(chart U) ⊗ V`, where `U` runs
through the invariant affine charts of `X` and `V` through the affine opens of `Y`
(`Work.SymQuot.RelQuot.pieceCoverQY`).

This file shows that this cover is *locally directed*: the pieces are ordered by inclusion of the
charts and of the affine opens of `Y`, and the transition map of `(U,V) ≤ (U',V')` is the
`pieceTrans` of `PieceMaps.lean`.  The two inputs are

* the transition maps are compatible with the cover maps, which is `pieceTrans_comp`;
* a point of the intersection of two pieces lies in a common smaller piece: the `Y`-coordinate can
  be moved into an affine open inside the intersection of the two affine opens (affine opens form
  a basis of `Y`), and the `(X/Γ)`-coordinate into the chart of `U ⊓ U'` (the chart inclusion
  `chart U ⟶ X/Γ` is an open immersion whose preimage under the quotient map is exactly `U`).

The last two facts are the content of the local refinement lemma below.
-/
import Mathlib
import Submission.Work.SymQuot.RelQuot.Cover
import Submission.Work.SymQuot.RelQuot.PieceMaps
import Submission.Work.SymQuot.Chart.quotientMap_isIntegralHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Work.SymQuot.RelQuot

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Classical MonoidalCategory

section Pieces

universe u

variable {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ] {X Y : Work.SpecLin.Sch K}

/-! ## The transition maps of the piece cover

The transition map of the piece cover for `a ≤ b` is the underlying scheme morphism of the
`Over (Spec K)`-morphism `pieceTrans`. -/

/-- **The transition map of the piece cover**, as a morphism of schemes. -/
noncomputable def pieceLdTrans (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    {a b : pieceIdx D Y} (h : a ≤ b) :
    (pieceCoverQY (X := X) (Y := Y) D hbase).X a
      ⟶ (pieceCoverQY (X := X) (Y := Y) D hbase).X b :=
  (pieceTrans D hbase h.1 h.2).left

private lemma chartResOv_refl (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    chartResOv D hbase (le_refl U) = 𝟙 (chartU D hbase U) := by
  apply Over.OverMorphism.ext
  rw [chartResOv_left, Over.id_left]
  exact Work.SymQuot.GAction.chartRes_id D.action U.1 U.2.2

private lemma ovVMap_refl {V : Y.left.affineOpens} :
    ovVMap (Y := Y) (le_refl V) = 𝟙 (ovV V) := by
  apply Over.OverMorphism.ext
  simp only [ovVMap_left, Over.id_left, ovV_left, Scheme.homOfLE_rfl]

/-- The `pieceTrans` of a reflexive inclusion is the identity. -/
private lemma pieceLdTrans_refl (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    (U : D.Chart) (V : Y.left.affineOpens) :
    pieceTrans D hbase (le_refl U) (le_refl V) = 𝟙 (chartU D hbase U ⊗ ovV V) := by
  rw [pieceTrans, chartResOv_refl, ovVMap_refl, MonoidalCategory.id_tensorHom,
    MonoidalCategory.whiskerLeft_id]

/-- `pieceLdTrans` of a reflexive inclusion is the identity. -/
private lemma pieceLdTrans_id (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (a : pieceIdx D Y) :
    pieceLdTrans D hbase (le_refl a)
      = 𝟙 ((pieceCoverQY (X := X) (Y := Y) D hbase).X a) := by
  have h := congrArg Over.Hom.left (pieceLdTrans_refl D hbase a.1 a.2)
  rw [Over.id_left] at h
  simpa only [pieceLdTrans] using h

/-- The transition maps of the piece cover compose. -/
private lemma pieceTrans_comp' (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    {U U' U'' : D.Chart} {V V' V'' : Y.left.affineOpens} (h₁ : U ≤ U') (h₂ : U' ≤ U'')
    (k₁ : V ≤ V') (k₂ : V' ≤ V'') :
    pieceTrans D hbase h₁ k₁ ≫ pieceTrans D hbase h₂ k₂
      = pieceTrans D hbase (h₁.trans h₂) (k₁.trans k₂) := by
  rw [pieceTrans, pieceTrans, pieceTrans, MonoidalCategory.tensorHom_comp_tensorHom]
  congr 1
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, chartResOv_left, chartResOv_left, chartResOv_left]
    exact Work.SymQuot.GAction.chartRes_comp D.action U.1 U'.1 U''.1 h₁ h₂
      U''.2.2 U'.2.2 U.2.2
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, ovVMap_left, ovVMap_left, ovVMap_left]
    exact Scheme.homOfLE_homOfLE Y.left k₁ k₂

/-- `pieceLdTrans` is compatible with composition. -/
private lemma pieceLdTrans_comp (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    {a b c : pieceIdx D Y} (h : a ≤ b) (h' : b ≤ c) :
    pieceLdTrans D hbase (h.trans h') = pieceLdTrans D hbase h ≫ pieceLdTrans D hbase h' := by
  have h2 := congrArg Over.Hom.left (pieceTrans_comp' D hbase h.1 h'.1 h.2 h'.2)
  rw [Over.comp_left] at h2
  simpa only [pieceLdTrans] using h2.symm

/-- The transition maps are compatible with the cover maps. -/
private lemma pieceLdTrans_w (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {a b : pieceIdx D Y} (h : a ≤ b) :
    pieceLdTrans D hbase h ≫ (pieceCoverQY (X := X) (Y := Y) D hbase).f b
      = (pieceCoverQY (X := X) (Y := Y) D hbase).f a := by
  have h2 := congrArg Over.Hom.left (pieceTrans_comp D hbase h.1 h.2)
  rw [Over.comp_left] at h2
  simpa only [pieceLdTrans] using h2

/-! ## The image of a piece

The image of the piece map `chart U ⊗ V ⟶ (X/Γ) ⊗ Y` is the product of the image of the chart
inclusion of `U` and of the open `V`. -/

private lemma range_f_pieceCoverQY (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (i : pieceIdx D Y) :
    Set.range ⇑((pieceCoverQY (X := X) (Y := Y) D hbase).f i)
      = ⇑(pullback.fst (relQuotScheme X D hbase).hom Y.hom) ⁻¹' Set.range ⇑(D.chartι i.1)
        ∩ ⇑(pullback.snd (relQuotScheme X D hbase).hom Y.hom) ⁻¹' Set.range ⇑(i.2.1.ι) := by
  rw [pieceCoverQY_f_eq, Over.tensorHom_left]
  exact Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _

/-- A point of `X` is mapped into the chart of an invariant affine open `U` of the quotient if
and only if it lies in `U` itself. -/
private lemma mem_range_chartι_iff (D : QuotientData Γ X.left) (W : D.Chart) (x : X.left) :
    D.quotientMap x ∈ Set.range ⇑(D.chartι W) ↔ x ∈ W.1 := by
  have hpre : x ∈ D.quotientMap ⁻¹ᵁ (Scheme.Hom.opensRange (D.chartι W)) ↔ x ∈ W.1 := by
    rw [QuotientData.quotientMap_preimage_opensRange_chartι D W]
  rw [← Scheme.Hom.coe_opensRange (D.chartι W)]
  exact ⟨fun h => hpre.mp ((Scheme.Hom.mem_preimage D.quotientMap).mpr h),
    fun h => (Scheme.Hom.mem_preimage D.quotientMap).mp (hpre.mpr h)⟩

/-! ## Refining two pieces at a common point -/

/-- **Two pieces of the cover of `(X/Γ) ⊗ Y` meeting at a point have a common smaller piece
containing that point.** -/
private lemma exists_le_of_mem_ranges (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    {i j : pieceIdx D Y} {t : ((relQuotScheme X D hbase) ⊗ Y).left}
    (ht : t ∈ Set.range ⇑((pieceCoverQY (X := X) (Y := Y) D hbase).f i)
      ∩ Set.range ⇑((pieceCoverQY (X := X) (Y := Y) D hbase).f j)) :
    ∃ k : pieceIdx D Y, k ≤ i ∧ k ≤ j ∧
      t ∈ Set.range ⇑((pieceCoverQY (X := X) (Y := Y) D hbase).f k) := by
  rw [range_f_pieceCoverQY D hbase i, Set.mem_inter_iff] at ht
  obtain ⟨⟨hti₁, hti₂⟩, htj⟩ := ht
  rw [range_f_pieceCoverQY D hbase j, Set.mem_inter_iff] at htj
  obtain ⟨htj₁, htj₂⟩ := htj
  -- the `X/Γ`-coordinate of `t`
  obtain ⟨a, ha⟩ := D.quotientMap_surjective
    (pullback.fst (relQuotScheme X D hbase).hom Y.hom t)
  have haU : a ∈ i.1.1 :=
    (mem_range_chartι_iff D i.1 a).mp (by
      have h : pullback.fst (relQuotScheme X D hbase).hom Y.hom t
          ∈ Set.range ⇑(D.chartι i.1) := hti₁
      rwa [← ha] at h)
  have haU' : a ∈ j.1.1 :=
    (mem_range_chartι_iff D j.1 a).mp (by
      have h : pullback.fst (relQuotScheme X D hbase).hom Y.hom t
          ∈ Set.range ⇑(D.chartι j.1) := htj₁
      rwa [← ha] at h)
  -- the `Y`-coordinate of `t`
  have ht₂i : pullback.snd (relQuotScheme X D hbase).hom Y.hom t ∈ i.2.1 := by
    have h : pullback.snd (relQuotScheme X D hbase).hom Y.hom t ∈ Set.range ⇑(i.2.1.ι) := hti₂
    rwa [Scheme.Opens.range_ι] at h
  have ht₂j : pullback.snd (relQuotScheme X D hbase).hom Y.hom t ∈ j.2.1 := by
    have h : pullback.snd (relQuotScheme X D hbase).hom Y.hom t ∈ Set.range ⇑(j.2.1.ι) := htj₂
    rwa [Scheme.Opens.range_ι] at h
  obtain ⟨S, ⟨V, hVmem, rfl⟩, ht₂V, hVsub⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show pullback.snd (relQuotScheme X D hbase).hom Y.hom t ∈ i.2.1 ⊓ j.2.1 from ⟨ht₂i, ht₂j⟩)
    (i.2.1 ⊓ j.2.1).isOpen
  refine ⟨(D.inf i.1 j.1, ⟨V, hVmem⟩), ?_, ?_, ?_⟩
  · -- `D.inf i.1 j.1 ≤ i.1` and `V ≤ i.2`
    refine ⟨?_, ?_⟩
    · show (D.inf i.1 j.1).1 ≤ i.1.1
      exact inf_le_left
    · exact fun x hx => (hVsub hx).1
  · refine ⟨?_, ?_⟩
    · show (D.inf i.1 j.1).1 ≤ j.1.1
      exact inf_le_right
    · exact fun x hx => (hVsub hx).2
  · rw [range_f_pieceCoverQY D hbase (D.inf i.1 j.1, ⟨V, hVmem⟩), Set.mem_inter_iff]
    refine ⟨?_, ?_⟩
    · have h : pullback.fst (relQuotScheme X D hbase).hom Y.hom t
          ∈ Set.range ⇑(D.chartι (D.inf i.1 j.1)) := by
        rw [← ha]
        exact (mem_range_chartι_iff D (D.inf i.1 j.1) a).mpr (by
          show a ∈ i.1.1 ⊓ j.1.1
          exact ⟨haU, haU'⟩)
      exact h
    · rw [Scheme.Opens.range_ι]
      exact ht₂V

/-! ## Local directedness of the cover -/

private lemma pieceLd_directed_aux (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {i j : pieceIdx D Y}
    (x : (pullback ((pieceCoverQY (X := X) (Y := Y) D hbase).f i)
      ((pieceCoverQY (X := X) (Y := Y) D hbase).f j)).carrier) :
    ∃ (k : pieceIdx D Y) (hki : k ≤ i) (hkj : k ≤ j)
      (y : (pieceCoverQY (X := X) (Y := Y) D hbase).X k),
      pullback.lift (pieceLdTrans D hbase hki) (pieceLdTrans D hbase hkj)
        (by rw [pieceLdTrans_w D hbase hki, pieceLdTrans_w D hbase hkj]) y = x := by
  haveI hi : IsOpenImmersion ((pieceCoverQY (X := X) (Y := Y) D hbase).f i) :=
    pieceMap_isOpenImmersion D hbase i.1 i.2
  haveI hj : IsOpenImmersion ((pieceCoverQY (X := X) (Y := Y) D hbase).f j) :=
    pieceMap_isOpenImmersion D hbase j.1 j.2
  have hcond : (pieceCoverQY (X := X) (Y := Y) D hbase).f i
        (pullback.fst ((pieceCoverQY (X := X) (Y := Y) D hbase).f i)
          ((pieceCoverQY (X := X) (Y := Y) D hbase).f j) x)
      = (pieceCoverQY (X := X) (Y := Y) D hbase).f j
        (pullback.snd ((pieceCoverQY (X := X) (Y := Y) D hbase).f i)
          ((pieceCoverQY (X := X) (Y := Y) D hbase).f j) x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun φ => φ x) (pullback.condition
      (f := (pieceCoverQY (X := X) (Y := Y) D hbase).f i)
      (g := (pieceCoverQY (X := X) (Y := Y) D hbase).f j))
  have ht : (pieceCoverQY (X := X) (Y := Y) D hbase).f i
        (pullback.fst ((pieceCoverQY (X := X) (Y := Y) D hbase).f i)
          ((pieceCoverQY (X := X) (Y := Y) D hbase).f j) x)
      ∈ Set.range ⇑((pieceCoverQY (X := X) (Y := Y) D hbase).f i)
        ∩ Set.range ⇑((pieceCoverQY (X := X) (Y := Y) D hbase).f j) :=
    ⟨⟨_, rfl⟩, ⟨_, hcond.symm⟩⟩
  obtain ⟨k, hki, hkj, htk⟩ := exists_le_of_mem_ranges D hbase ht
  obtain ⟨y, hy⟩ := htk
  refine ⟨k, hki, hkj, y, ?_⟩
  apply (Scheme.Hom.isOpenEmbedding (pullback.fst
    ((pieceCoverQY (X := X) (Y := Y) D hbase).f i)
    ((pieceCoverQY (X := X) (Y := Y) D hbase).f j))).injective
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  apply (Scheme.Hom.isOpenEmbedding ((pieceCoverQY (X := X) (Y := Y) D hbase).f i)).injective
  have h1 : (pieceCoverQY (X := X) (Y := Y) D hbase).f i (pieceLdTrans D hbase hki y)
      = (pieceCoverQY (X := X) (Y := Y) D hbase).f k y := by
    rw [← Scheme.Hom.comp_apply, pieceLdTrans_w D hbase hki]
  rw [h1, hy]

end Pieces

/-! ## The statement -/

universe u
open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem pieceCoverQY_locallyDirected {K : Type u} [Field K] {X Y : Work.SpecLin.Sch K}
    {Γ : Type u} [Group Γ] [Fintype Γ] (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) :
    ∃ ld : (Work.SymQuot.RelQuot.pieceCoverQY (X := X) (Y := Y) D hbase).LocallyDirected,
      ∀ {a b : D.Chart × Y.left.affineOpens} (h : a ⟶ b),
        ld.trans h = (Work.SymQuot.RelQuot.pieceTrans D hbase (leOfHom h).1 (leOfHom h).2).left := by
  refine ⟨{ trans := fun {a b} hij => pieceLdTrans D hbase (leOfHom hij),
            trans_id := fun i => pieceLdTrans_id D hbase i,
            trans_comp := fun hij hjk => pieceLdTrans_comp D hbase (leOfHom hij) (leOfHom hjk),
            w := fun hij => pieceLdTrans_w D hbase (leOfHom hij),
            directed := fun {i j} x => ?_,
            property_trans := fun hij =>
              isOpenImmersion_pieceTrans D hbase (leOfHom hij).1 (leOfHom hij).2 }, ?_⟩
  · obtain ⟨k, hki, hkj, y, hy⟩ := pieceLd_directed_aux D hbase x
    exact ⟨k, homOfLE hki, homOfLE hkj, y, hy⟩
  · intro a b h
    rfl

end Work.SymQuot.RelQuot
