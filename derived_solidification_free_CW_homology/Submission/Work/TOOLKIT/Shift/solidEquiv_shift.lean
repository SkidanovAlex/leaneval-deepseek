/-
AREA TOOLKIT — solid-equivalences are stable under shifting the source.

`SolidEquiv f` is the property that precomposition with `f` is bijective on
`Hom(-, iD.obj N)` for every `N : D(Solid)`.  This file shows that the property is
invariant under shifting `f`, i.e. under applying the shift autoequivalence of
`D(LightCondAb)` to `f`.  The two ingredients are pure category theory:

* `shift_precomp_bijective_iff`: in any category equipped with a `ℤ`-shift, the map
  `g ↦ f⟦n⟧' ≫ g` on `Hom(Y⟦n⟧, W)` is bijective if and only if the map
  `g ↦ f ≫ g` on `Hom(Y, W⟦-n⟧)` is.  Both `Hom` types are identified through the
  natural iso `(shiftFunctor C (-n)) ⋙ (shiftFunctor C n) ≅ 𝟭 C`, and the two
  precomposition maps are intertwined by these identifications, so bijectivity
  transfers.
* `precomp_iso_target`: bijectivity of `g ↦ f ≫ g` only depends on the target up to
  isomorphism (applied to the `CommShift` isomorphism
  `(iD.obj N)⟦-n⟧ ≅ iD.obj (N⟦-n⟧)` of the derived inclusion).
-/
import Mathlib
import Submission.Work.TOOLKIT.Basic

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.TOOLKIT.Shift

/-- Shifting the source: for any object `W` of a category with a `ℤ`-shift, precomposition
with `f⟦n⟧'` on `Hom(Y⟦n⟧, W)` is bijective if and only if precomposition with `f` on
`Hom(Y, W⟦-n⟧)` is. -/
theorem shift_precomp_bijective_iff {C : Type*} [Category* C] [HasShift C ℤ]
    {X Y : C} (f : X ⟶ Y) (W : C) (n : ℤ) :
    Function.Bijective (fun g : Y⟦n⟧ ⟶ W => f⟦n⟧' ≫ g) ↔
      Function.Bijective (fun h : Y ⟶ W⟦-n⟧ => f ≫ h) := by
  have hn : (-n) + n = 0 := by ring
  -- the natural isomorphism `shift(-n) ⋙ shift(n) ≅ 𝟭`
  let e : shiftFunctor C (-n) ⋙ shiftFunctor C n ≅ 𝟭 C := shiftFunctorCompIsoId C (-n) n hn
  -- the bijection `Hom(Z, W⟦-n⟧) ≃ Hom(Z⟦n⟧, W)`: shift, then cancel the shift on the target
  let ψ : ∀ Z : C, (Z ⟶ W⟦-n⟧) ≃ (Z⟦n⟧ ⟶ W) := fun Z =>
    (Equiv.ofBijective (fun h : Z ⟶ W⟦-n⟧ => (shiftFunctor C n).map h)
      ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩).trans
      (Iso.homCongr (Iso.refl (Z⟦n⟧)) (e.app W))
  have hψ : ∀ (Z : C) (h : Z ⟶ W⟦-n⟧), ψ Z h = (shiftFunctor C n).map h ≫ (e.app W).hom := by
    intro Z h
    simp only [ψ, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
    rfl
  -- the two precomposition maps are intertwined by `ψ`: this is pure functoriality of the shift
  have key : ∀ h : Y ⟶ W⟦-n⟧, f⟦n⟧' ≫ ψ Y h = ψ X (f ≫ h) := by
    intro h
    rw [hψ X (f ≫ h), hψ Y h, Functor.map_comp, Category.assoc]
  have h2 : Function.Bijective ((fun g : Y⟦n⟧ ⟶ W => f⟦n⟧' ≫ g) ∘ (ψ Y)) ↔
      Function.Bijective (fun h : Y ⟶ W⟦-n⟧ => f ≫ h) := by
    have heq : ((fun g : Y⟦n⟧ ⟶ W => f⟦n⟧' ≫ g) ∘ (ψ Y)) =
        ((ψ X) ∘ (fun h : Y ⟶ W⟦-n⟧ => f ≫ h)) := by
      funext h; exact key h
    rw [heq]
    exact Function.Bijective.of_comp_iff' (ψ X).bijective (fun h : Y ⟶ W⟦-n⟧ => f ≫ h)
  have h1 : Function.Bijective (fun g : Y⟦n⟧ ⟶ W => f⟦n⟧' ≫ g) ↔
      Function.Bijective ((fun g : Y⟦n⟧ ⟶ W => f⟦n⟧' ≫ g) ∘ (ψ Y)) :=
    (Equiv.bijective_comp (ψ Y) (fun g : Y⟦n⟧ ⟶ W => f⟦n⟧' ≫ g)).symm
  exact h1.trans h2

/-- Changing the target up to isomorphism: if `e : W ≅ W'` then precomposition with `f` is
bijective on `Hom(Y, W)` if and only if it is bijective on `Hom(Y, W')`. -/
theorem precomp_iso_target {C : Type*} [Category* C] {X Y W W' : C} (f : X ⟶ Y) (e : W ≅ W') :
    Function.Bijective (fun g : Y ⟶ W => f ≫ g) ↔
      Function.Bijective (fun g : Y ⟶ W' => f ≫ g) := by
  let Φ : (Y ⟶ W) ≃ (Y ⟶ W') := Iso.homCongr (Iso.refl Y) e
  let Ψ : (X ⟶ W) ≃ (X ⟶ W') := Iso.homCongr (Iso.refl X) e
  have key : ∀ g : Y ⟶ W', (fun g : Y ⟶ W => f ≫ g) (Φ.symm g) = Ψ.symm (f ≫ g) := by
    intro g
    simp only [Φ, Ψ, Iso.homCongr_symm, Iso.refl_symm, Iso.homCongr_apply, Iso.symm_hom,
      Iso.refl_inv, Category.id_comp, Category.assoc]
  have h1 : Function.Bijective (fun g : Y ⟶ W => f ≫ g) ↔
      Function.Bijective ((fun g : Y ⟶ W => f ≫ g) ∘ Φ.symm) :=
    (Equiv.bijective_comp Φ.symm (fun g : Y ⟶ W => f ≫ g)).symm
  have h2 : Function.Bijective ((fun g : Y ⟶ W => f ≫ g) ∘ Φ.symm) ↔
      Function.Bijective (fun g : Y ⟶ W' => f ≫ g) := by
    have heq : ((fun g : Y ⟶ W => f ≫ g) ∘ Φ.symm) =
        (Ψ.symm ∘ (fun g : Y ⟶ W' => f ≫ g)) := by
      funext g; exact key g
    rw [heq]
    exact Function.Bijective.of_comp_iff' (Ψ.symm).bijective (fun g : Y ⟶ W' => f ≫ g)
  exact h1.trans h2

/-- Solid-equivalences are stable under shifting the source: if `f : X ⟶ Y` in `D(LightCondAb)`
induces bijections on `Hom(-, iD.obj N)` by precomposition, then so does its shift
`f⟦n⟧' : X⟦n⟧ ⟶ Y⟦n⟧`.  This uses the shift equivalence of the derived category and the fact
that the derived inclusion commutes with the shift (its `CommShift` instance). -/
theorem solidEquiv_shift {X Y : Work.TOOLKIT.DCat} {f : X ⟶ Y}
    (hf : Submission.Blueprint.SolidEquiv f) (n : ℤ) :
    Submission.Blueprint.SolidEquiv ((CategoryTheory.shiftFunctor Work.TOOLKIT.DCat n).map f) := by
  intro N
  -- move the shift from the source to the target
  rw [shift_precomp_bijective_iff f (Work.TOOLKIT.iD.obj N) n]
  -- `(iD.obj N)⟦-n⟧ ≅ iD.obj (N⟦-n⟧)` because `iD` commutes with the shift
  exact (precomp_iso_target f ((Work.TOOLKIT.iD.commShiftIso (-n)).app N).symm).mpr
    (hf (N⟦-n⟧))

end Work.TOOLKIT.Shift
