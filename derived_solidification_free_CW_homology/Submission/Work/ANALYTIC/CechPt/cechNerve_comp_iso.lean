import Mathlib

/-!
# The Čech nerve commutes with functors preserving the relevant wide pullbacks

For a functor `G : C ⥤ D` and an arrow `f : Arrow C`, the Čech nerve of `f` is built out of the
wide pullbacks of `f.hom` along itself.  If `G` preserves those wide pullbacks, then
`G` applied to the Čech nerve of `f` is canonically isomorphic to the Čech nerve of the image
arrow `Arrow.mk (G.map f.hom)`:

`Arrow.cechNerve f ⋙ G ≅ Arrow.cechNerve (Arrow.mk (G.map f.hom))`.

The isomorphism is the canonical comparison of limits
(`CategoryTheory.Limits.preservesLimitIso`); the only input about the Čech nerve itself is that its
structure maps are the `WidePullback.lift` maps, so that the comparison is compatible with them
(`cechPullIso_hom_lift`).
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits

set_option linter.style.haveILetI false

universe u v

variable {C : Type*} {D : Type*} [Category C] [Category D]

noncomputable section

/-- The diagram of a wide cospan is carried by a functor preserving the relevant limits to the
diagram of the wide cospan of the images.  The components of the isomorphism are identities; only
the structure morphisms `Hom.term` need the action of the functor to be compared. -/
def cechWideCospanIso (G : C ⥤ D) {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B) :
    WidePullbackShape.wideCospan B objs arrows ⋙ G ≅
      WidePullbackShape.wideCospan (G.obj B) (fun j => G.obj (objs j)) (fun j => G.map (arrows j)) :=
  WidePullbackShape.functorExt (Iso.refl _) (fun _ => Iso.refl _)

lemma cechWideCospanIso_hom_app_some (G : C ⥤ D) {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B) (i : J) :
    (cechWideCospanIso G B objs arrows).hom.app (some i) = 𝟙 _ := by
  simp only [cechWideCospanIso, WidePullbackShape.functorExt]
  rfl

lemma cechWideCospanIso_hom_app_none (G : C ⥤ D) {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B) :
    (cechWideCospanIso G B objs arrows).hom.app none = 𝟙 _ := by
  simp only [cechWideCospanIso, WidePullbackShape.functorExt]
  rfl

/-- Comparison of a wide pullback along a functor preserving this shape of limits with the wide
pullback of the images. -/
def cechPullIso (G : C ⥤ D) {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B)
    [h1 : HasWidePullback B objs arrows]
    [h2 : HasWidePullback (G.obj B) (fun j => G.obj (objs j)) (fun j => G.map (arrows j))]
    [h3 : PreservesLimitsOfShape (WidePullbackShape J) G] :
    G.obj (widePullback B objs arrows) ≅
      widePullback (G.obj B) (fun j => G.obj (objs j)) (fun j => G.map (arrows j)) :=
  preservesLimitIso G (WidePullbackShape.wideCospan B objs arrows) ≪≫
    HasLimit.isoOfNatIso (cechWideCospanIso G B objs arrows)

lemma cechPullIso_hom_π (G : C ⥤ D) {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B)
    [h1 : HasWidePullback B objs arrows]
    [h2 : HasWidePullback (G.obj B) (fun j => G.obj (objs j)) (fun j => G.map (arrows j))]
    [h3 : PreservesLimitsOfShape (WidePullbackShape J) G] (j : J) :
    (cechPullIso G B objs arrows).hom ≫ WidePullback.π (fun j => G.map (arrows j)) j
      = G.map (WidePullback.π arrows j) := by
  rw [cechPullIso, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
    cechWideCospanIso_hom_app_some, Category.comp_id, preservesLimitIso_hom_π]

lemma cechPullIso_hom_base (G : C ⥤ D) {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B)
    [h1 : HasWidePullback B objs arrows]
    [h2 : HasWidePullback (G.obj B) (fun j => G.obj (objs j)) (fun j => G.map (arrows j))]
    [h3 : PreservesLimitsOfShape (WidePullbackShape J) G] :
    (cechPullIso G B objs arrows).hom ≫ WidePullback.base (fun j => G.map (arrows j))
      = G.map (WidePullback.base arrows) := by
  rw [cechPullIso, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
    cechWideCospanIso_hom_app_none, Category.comp_id, preservesLimitIso_hom_π]

/-- Naturality of the comparison isomorphism with respect to `WidePullback.lift`. -/
lemma cechPullIso_hom_lift (G : C ⥤ D) {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B)
    [h1 : HasWidePullback B objs arrows]
    [h2 : HasWidePullback (G.obj B) (fun j => G.obj (objs j)) (fun j => G.map (arrows j))]
    [h3 : PreservesLimitsOfShape (WidePullbackShape J) G]
    {X : C} (a : X ⟶ B) (bs : ∀ j : J, X ⟶ objs j) (w : ∀ j : J, bs j ≫ arrows j = a) :
    G.map (WidePullback.lift a bs w) ≫ (cechPullIso G B objs arrows).hom
      = WidePullback.lift (G.map a) (fun j => G.map (bs j))
          (by intro j; rw [← G.map_comp, w]) := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, cechPullIso_hom_π, ← G.map_comp, WidePullback.lift_π, WidePullback.lift_π]
  · rw [Category.assoc, cechPullIso_hom_base, ← G.map_comp, WidePullback.lift_base,
      WidePullback.lift_base]

namespace CechNerveComp

/-- The `n`-th component of the comparison isomorphism between the Čech nerve of `f` composed
with `G` and the Čech nerve of the image arrow: a comparison of the two wide pullbacks. -/
def app (G : C ⥤ D) (f : Arrow C) (m : SimplexCategoryᵒᵖ)
    [h1 : HasWidePullback f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom)]
    [h2 : HasWidePullback (G.obj f.right) (fun _ : Fin (m.unop.len + 1) => G.obj f.left)
      (fun _ => G.map f.hom)]
    [h3 : PreservesLimitsOfShape (WidePullbackShape (Fin (m.unop.len + 1))) G] :
    G.obj (widePullback f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom)) ≅
      widePullback (G.obj f.right) (fun _ : Fin (m.unop.len + 1) => G.obj f.left)
        (fun _ => G.map f.hom) :=
  cechPullIso G f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom)

lemma app_hom_π (G : C ⥤ D) (f : Arrow C) (m : SimplexCategoryᵒᵖ)
    [h1 : HasWidePullback f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom)]
    [h2 : HasWidePullback (G.obj f.right) (fun _ : Fin (m.unop.len + 1) => G.obj f.left)
      (fun _ => G.map f.hom)]
    [h3 : PreservesLimitsOfShape (WidePullbackShape (Fin (m.unop.len + 1))) G]
    (j : Fin (m.unop.len + 1)) :
    (app G f m).hom ≫
        WidePullback.π (fun _ : Fin (m.unop.len + 1) => G.map f.hom) j
      = G.map (WidePullback.π (fun _ : Fin (m.unop.len + 1) => f.hom) j) := by
  simp only [app]
  exact cechPullIso_hom_π G f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom) j

lemma app_hom_base (G : C ⥤ D) (f : Arrow C) (m : SimplexCategoryᵒᵖ)
    [h1 : HasWidePullback f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom)]
    [h2 : HasWidePullback (G.obj f.right) (fun _ : Fin (m.unop.len + 1) => G.obj f.left)
      (fun _ => G.map f.hom)]
    [h3 : PreservesLimitsOfShape (WidePullbackShape (Fin (m.unop.len + 1))) G] :
    (app G f m).hom ≫
        WidePullback.base (fun _ : Fin (m.unop.len + 1) => G.map f.hom)
      = G.map (WidePullback.base (fun _ : Fin (m.unop.len + 1) => f.hom)) := by
  simp only [app]
  exact cechPullIso_hom_base G f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom)

lemma app_hom_lift (G : C ⥤ D) (f : Arrow C) (m : SimplexCategoryᵒᵖ)
    [h1 : HasWidePullback f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom)]
    [h2 : HasWidePullback (G.obj f.right) (fun _ : Fin (m.unop.len + 1) => G.obj f.left)
      (fun _ => G.map f.hom)]
    [h3 : PreservesLimitsOfShape (WidePullbackShape (Fin (m.unop.len + 1))) G]
    {X : C} (a : X ⟶ f.right) (bs : ∀ _ : Fin (m.unop.len + 1), X ⟶ f.left)
    (w : ∀ j : Fin (m.unop.len + 1), bs j ≫ f.hom = a) :
    G.map (WidePullback.lift a bs w) ≫ (app G f m).hom
      = WidePullback.lift (G.map a) (fun j => G.map (bs j))
          (by intro j; rw [← G.map_comp, w]) := by
  simp only [app]
  exact cechPullIso_hom_lift G f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom)
    a bs w

end CechNerveComp

/-- The canonical comparison isomorphism between the Čech nerve of `f` composed with a functor `G`
and the Čech nerve of the image arrow, when `G` preserves the wide pullbacks involved. -/
def cechNerveCompIso (G : C ⥤ D) (f : Arrow C)
    [hF : ∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)]
    [hG : ∀ n : ℕ, HasWidePullback
      (Arrow.mk (G.map f.hom)).right
      (fun _ : Fin (n + 1) => (Arrow.mk (G.map f.hom)).left)
      (fun _ : Fin (n + 1) => (Arrow.mk (G.map f.hom)).hom)]
    [hP : ∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1))) G] :
    Arrow.cechNerve f ⋙ G ≅ Arrow.cechNerve (Arrow.mk (G.map f.hom)) := by
  refine NatIso.ofComponents
    (fun n => CechNerveComp.app G f n (h1 := hF n.unop.len) (h2 := hG n.unop.len)
      (h3 := hP n.unop.len)) ?_
  intro n m g
  haveI hn1 : HasWidePullback f.right (fun _ : Fin (n.unop.len + 1) => f.left) (fun _ => f.hom) :=
    hF n.unop.len
  haveI hm1 : HasWidePullback f.right (fun _ : Fin (m.unop.len + 1) => f.left) (fun _ => f.hom) :=
    hF m.unop.len
  haveI hn2 : HasWidePullback (G.obj f.right) (fun _ : Fin (n.unop.len + 1) => G.obj f.left)
      (fun _ => G.map f.hom) := hG n.unop.len
  haveI hm2 : HasWidePullback (G.obj f.right) (fun _ : Fin (m.unop.len + 1) => G.obj f.left)
      (fun _ => G.map f.hom) := hG m.unop.len
  haveI hn3 : PreservesLimitsOfShape (WidePullbackShape (Fin (n.unop.len + 1))) G := hP n.unop.len
  haveI hm3 : PreservesLimitsOfShape (WidePullbackShape (Fin (m.unop.len + 1))) G := hP m.unop.len
  simp only [Functor.comp_map, Arrow.cechNerve_map, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right]
  rw [CechNerveComp.app_hom_lift]
  apply WidePullback.hom_ext
  · intro j
    rw [WidePullback.lift_π, Category.assoc, WidePullback.lift_π, CechNerveComp.app_hom_π]
  · rw [WidePullback.lift_base, Category.assoc, WidePullback.lift_base,
      CechNerveComp.app_hom_base]

end

theorem cechNerve_comp_iso {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (G : CategoryTheory.Functor C D) (f : CategoryTheory.Arrow C)
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePullback f.right (fun _ : Fin (n + 1) => f.left)
      (fun _ => f.hom)]
    [∀ n : ℕ, CategoryTheory.Limits.HasWidePullback
      (CategoryTheory.Arrow.mk (G.map f.hom)).right
      (fun _ : Fin (n + 1) => (CategoryTheory.Arrow.mk (G.map f.hom)).left)
      (fun _ : Fin (n + 1) => (CategoryTheory.Arrow.mk (G.map f.hom)).hom)]
    [∀ n : ℕ, CategoryTheory.Limits.PreservesLimitsOfShape
      (CategoryTheory.Limits.WidePullbackShape (Fin (n + 1))) G] :
    Nonempty (CategoryTheory.Iso
      (CategoryTheory.Functor.comp (CategoryTheory.Arrow.cechNerve f) G)
      (CategoryTheory.Arrow.cechNerve (CategoryTheory.Arrow.mk (G.map f.hom)))) :=
  ⟨cechNerveCompIso G f⟩

end Work.ANALYTIC.CechPt
