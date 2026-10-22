import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.Homotopy

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

/-!
# Homotopy invariance of `dFree` (CWIND/T5)

The functor `dFree : TopCat ⥤ DLightCondAb` sends a space `X` to `ℤ[X]` placed in degree `0`
of the derived category.  This file records the homotopy-invariance consequences of the analytic
input `HIProp` (homotopy invariance of `ℤ[-]` up to derived solidification), namely

* homotopic maps have the same status as solid-equivalences, and
* a homotopy equivalence of Hausdorff spaces induces a solid-equivalence.

The technical heart is that `dFree (i₀ Y)` and `dFree (i₁ Y)` — the two inclusions
`Y ⟶ Y × [0,1]` — share the one-sided inverse `dFree (pr : Y × [0,1] → Y)`; since `dFree` is a
functor the two maps are actually equal after composing with the projection, so the toolkit
(`ToolkitProp.of_comp_left`, `of_comp_right`) transports `HIProp`'s statement for `i₀` to `i₁`.
Homotopic maps factor through the two inclusions by `homotopy_factor`, and part (b) is then
two-out-of-three for the round trips of a homotopy equivalence, using `DerivedProp` to translate
`solid-equivalence` into invertibility after derived solidification.
-/

/-- `dFree` bundled as a functor; `dFree f = dFreeF.map f` holds definitionally. -/
noncomputable abbrev dFreeF : TopCat.{0} ⥤ DLightCondAb :=
  freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0

/-- `dFree` preserves composition. -/
lemma dFree_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dFree (f ≫ g) = dFree f ≫ dFree g :=
  Functor.map_comp dFreeF f g

/-- `dFree` preserves identities. -/
lemma dFree_id (X : TopCat.{0}) : dFree (𝟙 X) = 𝟙 (dFreeF.obj X) :=
  CategoryTheory.Functor.map_id dFreeF X

/-- A solid-equivalence can be cancelled on the left inside a composite: if `a` is a
solid-equivalence then `a ≫ q` is one exactly when `q` is. -/
lemma solidEquiv_comp_iff (hTK : ToolkitProp) {P Q R : DLightCondAb} (a : P ⟶ Q) (q : Q ⟶ R)
    (ha : SolidEquiv a) : SolidEquiv (a ≫ q) ↔ SolidEquiv q :=
  ⟨fun h => hTK.of_comp_left a q ha h, fun h => hTK.comp a q ha h⟩

/-- In a category, if both `a ≫ b` and `b ≫ a` are isomorphisms, then `a` is an isomorphism.
(A morphism with a left inverse and a right inverse is invertible, and the two hypotheses provide
such inverses.) -/
lemma isIso_of_isIso_comp_comp {C : Type*} [Category C] {P Q : C} (a : P ⟶ Q) (b : Q ⟶ P)
    (h₁ : IsIso (a ≫ b)) (h₂ : IsIso (b ≫ a)) : IsIso a := by
  have har : a ≫ (b ≫ inv (a ≫ b)) = 𝟙 P := by
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hla : (inv (b ≫ a) ≫ b) ≫ a = 𝟙 Q := by
    rw [Category.assoc, IsIso.inv_hom_id]
  have hrl : b ≫ inv (a ≫ b) = inv (b ≫ a) ≫ b := by
    calc b ≫ inv (a ≫ b)
        = 𝟙 Q ≫ (b ≫ inv (a ≫ b)) := (Category.id_comp _).symm
      _ = ((inv (b ≫ a) ≫ b) ≫ a) ≫ (b ≫ inv (a ≫ b)) := by rw [hla]
      _ = (inv (b ≫ a) ≫ b) ≫ (a ≫ (b ≫ inv (a ≫ b))) := by rw [Category.assoc]
      _ = (inv (b ≫ a) ≫ b) ≫ 𝟙 P := by rw [har]
      _ = inv (b ≫ a) ≫ b := Category.comp_id _
  exact ⟨b ≫ inv (a ≫ b), har, by rw [hrl, hla]⟩

/-- A homotopy `H : f.Homotopic g` between maps `f g : C(↥X, ↥Y)` factors through the two
inclusions `i₀, i₁ : X ⟶ X × [0,1]`: after swapping the coordinates of the homotopy
`[0,1] × X → Y` one gets a map `h : X × [0,1] ⟶ Y` with `f = i₀ X ≫ h` and `g = i₁ X ≫ h`. -/
lemma homotopy_factor {X Y : TopCat.{0}} {f g : C(↥X, ↥Y)} (H : ContinuousMap.Homotopy f g) :
    ∃ (h : TopCat.of (↥X × ↥unitInterval) ⟶ Y),
      TopCat.ofHom f = Submission.Blueprint.i₀ X ≫ h ∧
      TopCat.ofHom g = Work.CWIND.i₁ X ≫ h := by
  refine ⟨TopCat.ofHom ⟨fun p : ↥X × ↥unitInterval => H.toContinuousMap (p.2, p.1),
    H.toContinuousMap.continuous.comp continuous_swap⟩, ?_, ?_⟩
  · apply TopCat.ext
    intro x
    simp only [ConcreteCategory.hom_ofHom, TopCat.hom_comp, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, Submission.Blueprint.i₀]
    exact (H.map_zero_left x).symm
  · apply TopCat.ext
    intro x
    simp only [ConcreteCategory.hom_ofHom, TopCat.hom_comp, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, Work.CWIND.i₁]
    exact (H.map_one_left x).symm

/-- For a Hausdorff space `Y`, the inclusion `i₁ Y : Y ⟶ Y × [0,1]` induces a
solid-equivalence `ℤ[Y] ⟶ ℤ[Y × [0,1]]`.  It shares the one-sided inverse
`dFree (pr : Y × [0,1] → Y)` with `dFree (i₀ Y)`, which is a solid-equivalence by `HIProp`;
two-out-of-three (`ToolkitProp.of_comp_left`/`of_comp_right`) transports this to `i₁`. -/
lemma solidEquiv_dFree_i₁ (hHI : HIProp) (hTK : ToolkitProp) (Y : TopCat.{0}) [T2Space Y] :
    SolidEquiv (dFree (Work.CWIND.i₁ Y)) := by
  have hA : SolidEquiv (dFree (Submission.Blueprint.i₀ Y)) := hHI Y
  have hAP : dFree (Submission.Blueprint.i₀ Y) ≫ dFree (Work.CWIND.prI Y) =
      𝟙 (dFreeF.obj Y) := by
    rw [← dFree_comp, Work.CWIND.i₀_comp_prI, dFree_id]
  have hP : SolidEquiv (dFree (Work.CWIND.prI Y)) :=
    hTK.of_comp_left _ _ hA (by rw [hAP]; exact hTK.of_iso _ (IsIso.id _))
  have hBP : dFree (Work.CWIND.i₁ Y) ≫ dFree (Work.CWIND.prI Y) = 𝟙 (dFreeF.obj Y) := by
    rw [← dFree_comp, Work.CWIND.i₁_comp_prI, dFree_id]
  exact hTK.of_comp_right _ _ hP (by rw [hBP]; exact hTK.of_iso _ (IsIso.id _))

/-- **CWIND/T5. Homotopy invariance consequences of `HIProp`.**  Two facts about the functor
`dFree : TopCat ⥤ DLightCondAb`, `f ↦ ℤ[X]` placed in degree `0` of the derived category.

(a) Homotopic maps `f, g : X ⟶ Y` (with `X` Hausdorff) have the same status as solid-equivalences:
`SolidEquiv (dFree f) ↔ SolidEquiv (dFree g)`.  The proof: `HIProp` says `dFree (i₀ Y)` is a
solid-equivalence; `i₁ Y` is obtained from `i₀ Y` by a homeomorphism, and `dFree (i₀ Y)` and
`dFree (i₁ Y)` have the common one-sided inverse `dFree (pr : Y × [0,1] → Y)`, whence they have the
same image under `L`; a homotopy `X × [0,1] → Y` then shows that homotopic maps have the same image
under `L`, and `D.L.map f` being invertible is equivalent to `SolidEquiv f` by `DerivedProp`.

(b) Hence a homotopy equivalence `e : X ≃ₕ Y` between Hausdorff spaces gives a solid-equivalence
`dFree e.toFun`: compose the homotopy equivalences with their homotopy inverses and apply (a) to
`e.toFun ≫ e.invFun` and `e.invFun ≫ e.toFun`, both homotopic to the identity. -/
theorem dFree_homotopy (hD : DerivedProp) [isSolid.ι.IsRightAdjoint] (D : DerivedPackage)
    (hHI : HIProp) (hTK : ToolkitProp) :
    (∀ {X Y : TopCat.{0}} [T2Space X] {f g : C(↥X, ↥Y)}, ContinuousMap.Homotopic f g →
        (SolidEquiv (dFree (TopCat.ofHom f)) ↔ SolidEquiv (dFree (TopCat.ofHom g)))) ∧
      (∀ {X Y : TopCat.{0}} [T2Space X] [T2Space Y] (e : ContinuousMap.HomotopyEquiv ↥X ↥Y),
        SolidEquiv (dFree (TopCat.ofHom e.toFun))) := by
  have hA : ∀ {X Y : TopCat.{0}} [T2Space X] {f g : C(↥X, ↥Y)}, ContinuousMap.Homotopic f g →
      (SolidEquiv (dFree (TopCat.ofHom f)) ↔ SolidEquiv (dFree (TopCat.ofHom g))) := by
    intro X Y _ f g hfg
    obtain ⟨H⟩ := hfg
    obtain ⟨h, hf, hg⟩ := homotopy_factor H
    have hA₀ : SolidEquiv (dFree (Submission.Blueprint.i₀ X)) := hHI X
    have hB₀ : SolidEquiv (dFree (Work.CWIND.i₁ X)) := solidEquiv_dFree_i₁ hHI hTK X
    have e1 : dFree (TopCat.ofHom f) = dFree (Submission.Blueprint.i₀ X) ≫ dFree h := by
      rw [hf, dFree_comp]
    have e2 : dFree (TopCat.ofHom g) = dFree (Work.CWIND.i₁ X) ≫ dFree h := by
      rw [hg, dFree_comp]
    rw [e1, e2]
    exact (solidEquiv_comp_iff hTK _ _ hA₀).trans (solidEquiv_comp_iff hTK _ _ hB₀).symm
  refine ⟨hA, ?_⟩
  intro X Y _ _ e
  -- the two round trips of the homotopy equivalence, composed with `dFree`
  have hY : SolidEquiv (dFree (TopCat.ofHom (e.toFun.comp e.invFun))) := by
    refine (hA (X := Y) (Y := Y) (f := e.toFun.comp e.invFun)
      (g := ContinuousMap.id ↥Y) e.right_inv).mpr ?_
    rw [TopCat.ofHom_id, dFree_id]
    exact hTK.of_iso _ (IsIso.id _)
  have hX : SolidEquiv (dFree (TopCat.ofHom (e.invFun.comp e.toFun))) := by
    refine (hA (X := X) (Y := X) (f := e.invFun.comp e.toFun)
      (g := ContinuousMap.id ↥X) e.left_inv).mpr ?_
    rw [TopCat.ofHom_id, dFree_id]
    exact hTK.of_iso _ (IsIso.id _)
  -- translate into invertibility after derived solidification
  have i1 : IsIso (D.L.map (dFree (TopCat.ofHom e.toFun) ≫ dFree (TopCat.ofHom e.invFun))) := by
    rw [← dFree_comp, ← TopCat.ofHom_comp e.toFun e.invFun]
    exact (hD.2 D _).mp hX
  have i2 : IsIso (D.L.map (dFree (TopCat.ofHom e.invFun) ≫ dFree (TopCat.ofHom e.toFun))) := by
    rw [← dFree_comp, ← TopCat.ofHom_comp e.invFun e.toFun]
    exact (hD.2 D _).mp hY
  have j1 : IsIso (D.L.map (dFree (TopCat.ofHom e.toFun)) ≫
      D.L.map (dFree (TopCat.ofHom e.invFun))) := by
    rw [← show D.L.map (dFree (TopCat.ofHom e.toFun) ≫ dFree (TopCat.ofHom e.invFun)) =
        D.L.map (dFree (TopCat.ofHom e.toFun)) ≫ D.L.map (dFree (TopCat.ofHom e.invFun))
        from Functor.map_comp D.L _ _]
    exact i1
  have j2 : IsIso (D.L.map (dFree (TopCat.ofHom e.invFun)) ≫
      D.L.map (dFree (TopCat.ofHom e.toFun))) := by
    rw [← show D.L.map (dFree (TopCat.ofHom e.invFun) ≫ dFree (TopCat.ofHom e.toFun)) =
        D.L.map (dFree (TopCat.ofHom e.invFun)) ≫ D.L.map (dFree (TopCat.ofHom e.toFun))
        from Functor.map_comp D.L _ _]
    exact i2
  exact (hD.2 D _).mpr (isIso_of_isIso_comp_comp _ _ j1 j2)

end Work.CWIND.Homotopy
