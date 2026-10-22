/-
AREA RESOL — solid-cofibrant complexes are stable under isomorphism in `K(LightCondAb)`.

`SolidCofibrantH K` says that the localization `Qh : K(LightCondAb) ⥤ D(LightCondAb)`
induces a bijection on `Hom(K, hq (ιC.obj N))` for every complex `N` of solid objects.
Since `Qh` is a functor, conjugating by the two isomorphisms induced by an isomorphism
`e : K ≅ L` (on the hom sets in `K` and in `D`) identifies these two bijectivity statements:
this is `bijective_Qh_map_of_iso_source` below, the mirror image of
`bijective_Qh_map_of_iso_target` in `RESOL/solidCofibrantH_shift.lean`.

The main statement, `solidCofibrantH_of_iso`, is the `iso` field of `CofibrantClosure`.
-/
import Mathlib
import Submission.Work.RESOL.Basic

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.RESOL

/-- The bijectivity of the localization `DerivedCategory.Qh` on `Hom(-, L)` only depends on the
source up to isomorphism. -/
theorem bijective_Qh_map_of_iso_source {K K' L : KCat} (e : K ≅ K')
    (h : Function.Bijective (fun f : K ⟶ L => DerivedCategory.Qh.map f)) :
    Function.Bijective (fun f : K' ⟶ L => DerivedCategory.Qh.map f) := by
  -- precomposition with `e` on the homs of `K(LightCondAb)`
  let Φ : (K ⟶ L) ≃ (K' ⟶ L) := Iso.homCongr e (Iso.refl L)
  -- precomposition with `Qh.map e` on the homs of `D(LightCondAb)`
  let Ψ : (DerivedCategory.Qh.obj K ⟶ DerivedCategory.Qh.obj L) ≃
      (DerivedCategory.Qh.obj K' ⟶ DerivedCategory.Qh.obj L) :=
    Iso.homCongr (DerivedCategory.Qh.mapIso e) (Iso.refl (DerivedCategory.Qh.obj L))
  have key : ∀ f : K ⟶ L, Ψ (DerivedCategory.Qh.map f) = DerivedCategory.Qh.map (Φ f) := by
    intro f
    simp only [Φ, Ψ, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
      Functor.map_comp, Functor.mapIso_inv]
  have key2 : (fun f : K ⟶ L => Ψ (DerivedCategory.Qh.map f)) =
      (fun g : K' ⟶ L => DerivedCategory.Qh.map g) ∘ Φ.toFun := by
    funext f
    exact key f
  have h1 : Function.Bijective (fun f : K ⟶ L => Ψ (DerivedCategory.Qh.map f)) :=
    Function.Bijective.comp Ψ.bijective h
  rw [key2] at h1
  exact (Equiv.bijective_comp Φ (fun g : K' ⟶ L => DerivedCategory.Qh.map g)).mp h1

/-- Solid-cofibrant complexes are stable under isomorphism in `K(LightCondAb)`: this is the
`iso` field of `CofibrantClosure`. -/
theorem solidCofibrantH_of_iso {K L : Work.RESOL.KCat} (e : K ≅ L)
    (hK : Work.RESOL.SolidCofibrantH K) : Work.RESOL.SolidCofibrantH L := by
  intro N
  exact bijective_Qh_map_of_iso_source e (hK N)

end Work.RESOL
