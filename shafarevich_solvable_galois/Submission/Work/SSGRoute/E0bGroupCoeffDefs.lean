import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.E0bBarChange
import Submission.Work.SSGRoute.e0b_bridge
import Submission.Work.SSGRoute.projRes_homologyAddEquiv_extMk
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E0b (group-and-coefficient part): the group-change chain map on `Hom(barComplex, -)`

For `f : H →* G`, `A : Rep k G`, `B : Rep k H` and `φ : Rep.res f A ⟶ B`, this file provides

* `lyN k f φ n`, the degree-`n` linear map `(C_G.X n ⟶ A) →ₗ[k] (C_H.X n ⟶ B)`,
  `g ↦ barChange f n ≫ resMap f g ≫ φ`; and
* `lyMap k f φ`, the induced morphism of cochain complexes
  `(barComplex G).linearYonedaObj A ⟶ (barComplex H).linearYonedaObj B`.

The chain-level square `cochainsMap f φ ≫ inhomogeneousCochainsIso B = inhomogeneousCochainsIso A
≫ lyMap f φ` together with the naturality of `Bridge.Psi` (`e0b_bridge`) makes the
`Ext`/group-cohomology bridge natural in the group and the coefficients.
-/

open CategoryTheory

namespace Work.SSGRoute.E0bGC

noncomputable section

variable (k : Type) [CommRing k]

/-- The degree-`n` component of the group-and-coefficient change map on `Hom(barComplex, -)`:
precomposition with `barChange f n` and postcomposition with `φ`. -/
def lyN {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} k G} {B : Rep.{0} k H} (φ : Rep.res f A ⟶ B) (n : ℕ) :
    ((Rep.barComplex k G).X n ⟶ A) →ₗ[k] ((Rep.barComplex k H).X n ⟶ B) where
  toFun g := SSGRoute.PTExt.barChange k G H f n ≫ (Rep.resFunctor f).map g ≫ φ
  map_add' g h := by
    change SSGRoute.PTExt.barChange k G H f n ≫ (Rep.resFunctor f).map (g + h) ≫ φ =
      SSGRoute.PTExt.barChange k G H f n ≫ (Rep.resFunctor f).map g ≫ φ +
        SSGRoute.PTExt.barChange k G H f n ≫ (Rep.resFunctor f).map h ≫ φ
    rw [Functor.map_add (Rep.resFunctor f), Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r g := by
    change SSGRoute.PTExt.barChange k G H f n ≫ (Rep.resFunctor f).map (r • g) ≫ φ =
      r • (SSGRoute.PTExt.barChange k G H f n ≫ (Rep.resFunctor f).map g ≫ φ)
    rw [Functor.map_smul (F := Rep.resFunctor f), Linear.smul_comp, Linear.comp_smul]

@[simp]
lemma lyN_apply {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} k G} {B : Rep.{0} k H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (g : (Rep.barComplex k G).X n ⟶ A) :
    lyN k f φ n g = SSGRoute.PTExt.barChange k G H f n ≫
      (Rep.resFunctor f).map g ≫ φ := rfl

/-- **The group-and-coefficient change map** on the complexes of `Hom`s computing `Extⁿ(ℤ,−)`:
degreewise precomposition with `barChange f` and postcomposition with `φ`. -/
def lyMap {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} k G} {B : Rep.{0} k H} (φ : Rep.res f A ⟶ B) :
    (Rep.barComplex k G).linearYonedaObj k A ⟶
      (Rep.barComplex k H).linearYonedaObj k B where
  f n := ModuleCat.ofHom (lyN k f φ n)
  comm' i j hij := by
    obtain rfl : j = i + 1 := by rw [ComplexShape.up_Rel] at hij; exact hij.symm
    rw [ChainComplex.linearYonedaObj_d, ChainComplex.linearYonedaObj_d]
    change ModuleCat.ofHom (lyN k f φ i) ≫
        ModuleCat.ofHom (Linear.leftComp k B ((Rep.barComplex k H).d (i + 1) i)) =
      ModuleCat.ofHom (Linear.leftComp k A ((Rep.barComplex k G).d (i + 1) i)) ≫
        ModuleCat.ofHom (lyN k f φ (i + 1))
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
      ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
    apply LinearMap.ext
    intro g
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Linear.leftComp_apply, Linear.leftComp_apply,
      lyN_apply, lyN_apply]
    rw [Functor.map_comp (Rep.resFunctor f), Rep.barComplex.d_def (k := k) (G := G),
      Rep.barComplex.d_def (k := k) (G := H)]
    calc Rep.barComplex.d k H i ≫ SSGRoute.PTExt.barChange k G H f i ≫
          (Rep.resFunctor f).map g ≫ φ
        = (SSGRoute.PTExt.barChange k G H f (i + 1) ≫
            (Rep.resFunctor f).map (Rep.barComplex.d k G i)) ≫
              (Rep.resFunctor f).map g ≫ φ := by
            rw [SSGRoute.PTExt.barChange_chain]
            simp only [Category.assoc]
      _ = SSGRoute.PTExt.barChange k G H f (i + 1) ≫
            ((Rep.resFunctor f).map (Rep.barComplex.d k G i) ≫
              (Rep.resFunctor f).map g) ≫ φ := by
            simp only [Category.assoc]

@[simp]
lemma lyMap_f_apply {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} k G} {B : Rep.{0} k H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (g : (Rep.barComplex k G).X n ⟶ A) :
    (lyMap k f φ).f n g = SSGRoute.PTExt.barChange k G H f n ≫
      (Rep.resFunctor f).map g ≫ φ := by
  change (ModuleCat.Hom.hom (ModuleCat.ofHom (lyN k f φ n))) g = _
  rw [ModuleCat.hom_ofHom, lyN_apply]

end

end Work.SSGRoute.E0bGC
