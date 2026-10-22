import Mathlib
import Submission.Work.ANALYTIC.Basic

/-!
# Solid-equivalences are stable under binary biproducts

`Work.ANALYTIC.solidEquiv_biprod`: if `f : X ⟶ X'` and `g : Y ⟶ Y'` are solid-equivalences after
applying the free-object functor `ℤ[-] = single 0`, then so is the biproduct `biprod.map f g`.

The point of the statement is that `SolidEquiv` is tested by *precomposition* into the derived
inclusion of complexes of solid objects, so it is not a formal consequence of `f`, `g` being
isomorphisms: one has to relate the (derived) biproduct of two free objects to the free object on
the biproduct, which is what `Functor.mapBiprod` does.

The proof has three ingredients, each of which is independent of the specific objects:

* `mapBiprod_biprod_map`: for an *additive* functor `F`, the natural comparison
  `F.mapBiprod` intertwines `F.map (biprod.map f g)` with `biprod.map (F.map f) (F.map g)`.
  This is a general categorical fact, proved here by checking the two components.
* `cpx_biprod_solidEquiv`: at the level of complexes, the split short exact sequence
  `0 → A₁ → A₁ ⊞ A₂ → A₂ → 0` and the `ses₂` field of `ToolkitProp` give that a biproduct of
  solid-equivalences is a solid-equivalence.
* `solidEquiv_of_iso_square`: a solid-equivalence `d'` that is conjugated to `d` by a commuting
  square of isomorphisms makes `d` a solid-equivalence (composition and two-out-of-three).

Applying the first with the additive functor `CochainComplex.singleFunctor ℤ 0`, the second to its
two components, and the third to the resulting square in the derived category yields the result.
-/

open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC

open Submission.Blueprint

/-- The category of cochain complexes of light condensed abelian groups. -/
abbrev LCpx : Type 1 := CochainComplex LightCondAb ℤ

/-! ## The naturality square of `Functor.mapBiprod`

`Functor.mapBiprod F X Y` is the comparison `F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y`; for an additive
`F` it is an isomorphism, and the following is its naturality with respect to `biprod.map`. -/
lemma mapBiprod_biprod_map {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {X Y X' Y' : C} [HasBinaryBiproduct X Y]
    [HasBinaryBiproduct X' Y'] [HasBinaryBiproduct (F.obj X) (F.obj Y)]
    [HasBinaryBiproduct (F.obj X') (F.obj Y')] [PreservesBinaryBiproduct X Y F]
    [PreservesBinaryBiproduct X' Y' F] (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (biprod.map f g) ≫ (F.mapBiprod X' Y').hom =
      (F.mapBiprod X Y).hom ≫ biprod.map (F.map f) (F.map g) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.lift_fst_assoc,
      ← F.map_comp, biprod.map_fst]
  · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, biprod.lift_snd_assoc,
      ← F.map_comp, biprod.map_snd]

/-! ## Binary biproducts of solid-equivalences of complexes -/

/-- The split short complex `0 → A₁ → A₁ ⊞ A₂ → A₂ → 0`. -/
abbrev lcSplitSes (A₁ A₂ : LCpx) : ShortComplex LCpx :=
  ShortComplex.mk (biprod.inl : A₁ ⟶ A₁ ⊞ A₂) (biprod.snd : A₁ ⊞ A₂ ⟶ A₂) (by simp)

/-- The split short complex is short exact. -/
theorem lcSplitSes_shortExact (A₁ A₂ : LCpx) : (lcSplitSes A₁ A₂).ShortExact :=
  ShortComplex.Splitting.shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct A₁ A₂)

/-- A biproduct of solid-equivalences of complexes is a solid-equivalence. -/
theorem cpx_biprod_solidEquiv (hTK : ToolkitProp) {A₁ A₂ B₁ B₂ : LCpx} (f : A₁ ⟶ B₁)
    (g : A₂ ⟶ B₂) (hf : SolidEquiv (DerivedCategory.Q.map f))
    (hg : SolidEquiv (DerivedCategory.Q.map g)) :
    SolidEquiv (DerivedCategory.Q.map (biprod.map f g)) := by
  let φ : lcSplitSes A₁ A₂ ⟶ lcSplitSes B₁ B₂ :=
    { τ₁ := f, τ₂ := biprod.map f g, τ₃ := g, comm₁₂ := (biprod.inl_map f g).symm,
      comm₂₃ := biprod.map_snd f g }
  exact hTK.ses₂ (lcSplitSes_shortExact A₁ A₂) (lcSplitSes_shortExact B₁ B₂) φ hf hg

/-! ## Conjugation of solid-equivalences by isomorphisms -/

/-- A solid-equivalence is invariant under conjugation by a commuting square of isomorphisms. -/
theorem solidEquiv_of_iso_square (hTK : ToolkitProp) {A B A' B' : DLightCondAb} (d : A ⟶ B)
    (d' : A' ⟶ B') (e : A ≅ A') (e' : B ≅ B') (hsq : e.hom ≫ d' = d ≫ e'.hom)
    (hd' : SolidEquiv d') : SolidEquiv d := by
  have h1 : SolidEquiv (e.hom ≫ d') := hTK.comp e.hom d' (hTK.of_iso e.hom e.isIso_hom) hd'
  have h2 : SolidEquiv (d ≫ e'.hom) := hsq ▸ h1
  exact hTK.of_comp_right d e'.hom (hTK.of_iso e'.hom e'.isIso_hom) h2

/-! ## The comparison with the derived single functor -/

/-- The derived single functor is the composite of `CochainComplex.singleFunctor` with the
localization functor `Q`; this is `DerivedCategory.Q_map_single_map` in the form used below. -/
lemma Q_map_singleFunctor_map (X X' : LightCondAb) (f : X ⟶ X') :
    DerivedCategory.Q.map ((CochainComplex.singleFunctor LightCondAb 0).map f)
      = (DerivedCategory.singleFunctor LightCondAb 0).map f :=
  DerivedCategory.Q_map_single_map (C := LightCondAb) 0 f

/-! ## The main step -/

/-- If `S : LightCondAb ⥤ LCpx` is additive and `f`, `g` become solid-equivalences after applying
`S` and localizing, then `S.map (biprod.map f g)` is a solid-equivalence as well.  (For
`S = CochainComplex.singleFunctor LightCondAb 0` this is the statement
`Work.ANALYTIC.solidEquiv_biprod` up to the identification of the two single functors.) -/
theorem cpx_single_biprod (hTK : ToolkitProp) (S : LightCondAb ⥤ LCpx) [S.Additive]
    (X Y X' Y' : LightCondAb) (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : SolidEquiv (DerivedCategory.Q.map (S.map f)))
    (hg : SolidEquiv (DerivedCategory.Q.map (S.map g))) :
    SolidEquiv (DerivedCategory.Q.map (S.map (biprod.map f g))) := by
  have h1 : PreservesBinaryBiproduct X Y S :=
    Limits.preservesBinaryBiproduct_of_preservesBiproduct S X Y
  have h2 : PreservesBinaryBiproduct X' Y' S :=
    Limits.preservesBinaryBiproduct_of_preservesBiproduct S X' Y'
  have hsq := mapBiprod_biprod_map S f g
  have hsqQ : (DerivedCategory.Q.mapIso (S.mapBiprod X Y)).hom ≫
        DerivedCategory.Q.map (biprod.map (S.map f) (S.map g)) =
      DerivedCategory.Q.map (S.map (biprod.map f g)) ≫
        (DerivedCategory.Q.mapIso (S.mapBiprod X' Y')).hom := by
    rw [Functor.mapIso_hom, Functor.mapIso_hom, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp, hsq]
  refine solidEquiv_of_iso_square hTK (DerivedCategory.Q.map (S.map (biprod.map f g)))
    (DerivedCategory.Q.map (biprod.map (S.map f) (S.map g)))
    (DerivedCategory.Q.mapIso (S.mapBiprod X Y)) (DerivedCategory.Q.mapIso (S.mapBiprod X' Y'))
    hsqQ ?_
  exact cpx_biprod_solidEquiv hTK (S.map f) (S.map g) hf hg

/-- **Solid-equivalences are stable under binary biproducts.** -/
theorem solidEquiv_biprod (hTK : Submission.Blueprint.ToolkitProp) (X Y X' Y' : LightCondAb)
    (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map f))
    (hg : Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map g)) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (CategoryTheory.Limits.biprod.map f g)) := by
  have hf' : SolidEquiv
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor LightCondAb 0).map f)) := by
    rw [Q_map_singleFunctor_map]; exact hf
  have hg' : SolidEquiv
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor LightCondAb 0).map g)) := by
    rw [Q_map_singleFunctor_map]; exact hg
  have h := cpx_single_biprod hTK (CochainComplex.singleFunctor LightCondAb 0) X Y X' Y' f g
    hf' hg'
  rw [← Q_map_singleFunctor_map (X ⊞ Y) (X' ⊞ Y') (CategoryTheory.Limits.biprod.map f g)]
  exact h

end Work.ANALYTIC
