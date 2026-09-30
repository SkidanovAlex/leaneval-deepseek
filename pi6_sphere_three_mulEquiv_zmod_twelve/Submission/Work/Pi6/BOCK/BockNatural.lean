import Mathlib
import Submission.Work.Pi6.BOCK.BockExact
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# AREA BOCK — naturality of the Bockstein sequence

The maps `red` and `del` of the Bockstein long exact sequence are natural in the space: for a
continuous map `f : C(X, Y)` and all `n`,

* `red_Y ∘ f_* = f_* ∘ red_X` (coefficients `ℤ` on the source, `ℤ/p` on the target);
* `del_Y ∘ f_* = f_* ∘ del_X` (coefficients `ℤ/p` on the source, `ℤ` on the target).

Both follow from the naturality of the identification `eCIso'` (proved in `CoeffIso`), the
naturality of `H_n(C_*(X;ℤ) ⊗ ℤ) ≅ H_n(X;ℤ)`, and the naturality of the connecting map of a short
exact sequence of chain complexes (`HomologicalComplex.HomologySequence.δ_naturality`).
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.BOCK

noncomputable section

variable (p : ℕ)

/-- **The morphism of Bockstein short complexes induced by a continuous map.** -/
def bSESMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    bSES p X ⟶ bSES p Y where
  τ₁ := expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (𝟙_ (ModuleCat ℤ))
  τ₂ := expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (𝟙_ (ModuleCat ℤ))
  τ₃ := expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)
  comm₁₂ := expTensMapHom_expTensHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f)
    (Work.Pi6.EMZ.mulP p)
  comm₂₃ := expTensMapHom_expTensHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f)
    (Work.Pi6.EMZ.redP p)

/-- **Naturality of the connecting map.** -/
theorem delta_natural (hp : p.Prime) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) (n + 1) ≫
      delta p hp Y n =
    delta p hp X n ≫
      HomologicalComplex.homologyMap
        (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (𝟙_ (ModuleCat ℤ))) n :=
  (HomologicalComplex.HomologySequence.δ_naturality (bSESMap p f)
    (bSES_shortExact p hp X) (bSES_shortExact p hp Y) (n + 1) n
    (by rw [ComplexShape.down_Rel])).symm

/-- The inverse form of the naturality of the identification `eCIso'`. -/
theorem eCIso_natural_inv (hp : p.Prime) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    (Fp p).map (Work.Pi6.hmap (ZMod p) f n) ≫ (eCIso' p hp Y n).inv =
      (eCIso' p hp X n).inv ≫
        HomologicalComplex.homologyMap
          (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) n :=
  inv_naturality_of_square _ _ _ _ (eCIso_natural_mor p hp f n)

/-! ## Naturality of the reduction -/

/-- **Naturality of the reduction, as an equation of morphisms.** -/
theorem redMor_natural (hp : p.Prime) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    Work.Pi6.hmap ℤ f n ≫ redMor p hp Y n =
      redMor p hp X n ≫ (Fp p).map (Work.Pi6.hmap (ZMod p) f n) := by
  have h1 := expTensUnitHomologyIso_natural_inv f n
  have h2 : HomologicalComplex.homologyMap
        (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (𝟙_ (ModuleCat ℤ))) n ≫
        HomologicalComplex.homologyMap ((bSES p Y).g) n =
      HomologicalComplex.homologyMap ((bSES p X).g) n ≫
        HomologicalComplex.homologyMap
          (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) n := by
    have h := expTensMapHom_expTensHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f)
      (Work.Pi6.EMZ.redP p)
    have h' := congrArg (fun t => HomologicalComplex.homologyMap t n) h
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h'
    exact h'
  have h3 := eCIso_natural_mor p hp f n
  have e1 : Work.Pi6.hmap ℤ f n ≫ ((Work.Pi6.EMZ.expTensUnitHomologyIso Y n).inv ≫
      (HomologicalComplex.homologyMap ((bSES p Y).g) n ≫ (eCIso' p hp Y n).hom)) =
      (Work.Pi6.EMZ.expTensUnitHomologyIso X n).inv ≫
        (HomologicalComplex.homologyMap
          (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (𝟙_ (ModuleCat ℤ))) n ≫
          (HomologicalComplex.homologyMap ((bSES p Y).g) n ≫ (eCIso' p hp Y n).hom)) := by
    rw [← Category.assoc, h1, Category.assoc]
  have e2 : HomologicalComplex.homologyMap
        (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (𝟙_ (ModuleCat ℤ))) n ≫
        (HomologicalComplex.homologyMap ((bSES p Y).g) n ≫ (eCIso' p hp Y n).hom) =
      HomologicalComplex.homologyMap ((bSES p X).g) n ≫
        (HomologicalComplex.homologyMap
          (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) n ≫
          (eCIso' p hp Y n).hom) := by
    rw [← Category.assoc, h2, Category.assoc]
  simp only [redMor, Category.assoc]
  rw [e1, e2, h3]
  rfl

/-- **Naturality of the reduction.** -/
theorem redHom_natural (hp : p.Prime) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (x : Work.Pi6.HR ℤ X n) :
    redHom p hp Y n ((Work.Pi6.hmap ℤ f n).hom x) =
      (Work.Pi6.hmap (ZMod p) f n).hom (redHom p hp X n x) := by
  have hmor := redMor_natural p hp f n
  have hx := congrArg (fun t : Work.Pi6.HR ℤ X n ⟶ (Fp p).obj (Work.Pi6.HR (ZMod p) Y n) =>
      (ModuleCat.Hom.hom t) x) hmor
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  exact hx

/-! ## Naturality of the connecting map -/

/-- **Naturality of the connecting map, as an equation of morphisms.** -/
theorem delMor_natural (hp : p.Prime) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    (Fp p).map (Work.Pi6.hmap (ZMod p) f (n + 1)) ≫ delMor p hp Y n =
      delMor p hp X n ≫ Work.Pi6.hmap ℤ f n := by
  have h1 := eCIso_natural_inv p hp f (n + 1)
  have h2 := delta_natural p hp f n
  have h3 := expTensUnitHomologyIso_natural f n
  have e1 : (Fp p).map (Work.Pi6.hmap (ZMod p) f (n + 1)) ≫
      ((eCIso' p hp Y (n + 1)).inv ≫ (delta p hp Y n ≫
        (Work.Pi6.EMZ.expTensUnitHomologyIso Y n).hom)) =
      (eCIso' p hp X (n + 1)).inv ≫
        (HomologicalComplex.homologyMap
          (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) (n + 1) ≫
          (delta p hp Y n ≫ (Work.Pi6.EMZ.expTensUnitHomologyIso Y n).hom)) := by
    rw [← Category.assoc, h1, Category.assoc]
  have e2 : HomologicalComplex.homologyMap
        (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (Mp p)) (n + 1) ≫
        (delta p hp Y n ≫ (Work.Pi6.EMZ.expTensUnitHomologyIso Y n).hom) =
      delta p hp X n ≫
        (HomologicalComplex.homologyMap
          (expTensMapHom (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.chZ Y) (chMapZ f) (𝟙_ (ModuleCat ℤ))) n ≫
          (Work.Pi6.EMZ.expTensUnitHomologyIso Y n).hom) := by
    rw [← Category.assoc, h2, Category.assoc]
  simp only [delMor, Category.assoc]
  rw [e1, e2, h3]

/-- **Naturality of the connecting map.** -/
theorem delHom_natural (hp : p.Prime) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (y : Work.Pi6.HR (ZMod p) X (n + 1)) :
    delHom p hp Y n ((Work.Pi6.hmap (ZMod p) f (n + 1)).hom y) =
      (Work.Pi6.hmap ℤ f n).hom (delHom p hp X n y) := by
  have hmor := delMor_natural p hp f n
  have hx := congrArg (fun t : (Fp p).obj (Work.Pi6.HR (ZMod p) X (n + 1)) ⟶ Work.Pi6.HR ℤ Y n =>
      (ModuleCat.Hom.hom t) y) hmor
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  exact hx

end

end Work.Pi6.BOCK
