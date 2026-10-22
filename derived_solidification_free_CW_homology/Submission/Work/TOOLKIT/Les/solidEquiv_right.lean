import Mathlib
import Submission.Work.TOOLKIT.Basic

/-!
# Two-out-of-three for the contravariant long exact sequence (right column)

This file proves `solidEquiv_right` for the area TOOLKIT: for a morphism of distinguished
triangles `ψ : T₁ ⟶ T₂` in `D(LightCondAb)`, if precomposition with `ψ.hom₁` and with
`ψ.hom₂` is bijective on morphisms into the derived inclusion of every shift of a fixed
solid object `N`, then so is precomposition with `ψ.hom₃` (at the shift asked for).

The mathematical content is the five lemma applied to the morphism of long exact sequences
`Hom(-, W⟦n⟧)` attached to `ψ`, where `W = iD.obj N`.

The formalisation goes as follows.

* `yonMor f C` is the Yoneda image in `AddCommGrpCat` of `fᵒᵖ`, i.e. the morphism
  `Hom(Y,C) ⟶ Hom(X,C)` given by `u ↦ f ≫ u`; its underlying function is `f ≫ -`
  (`yonMor_fun`).
* `les_two_of_three` is the abstract statement: for distinguished triangles `T₁`, `T₂` and a
  morphism `ψ : T₁ ⟶ T₂` of triangles, the long exact sequences of `Hom(-, W⟦n⟧)` satisfy
  two-out-of-three at the third object.  The ladder is a morphism of six-term exact sequences
  obtained from `homologySequenceComposableArrows₅` (exactness:
  `homologySequenceComposableArrows₅_exact`) and the op-triangle equivalence
  (`TriangleOpEquivalence.functor`), whose triangle axioms give the four "linear" squares,
  while the square at the connecting maps is `Functor.homologySequenceδ_naturality`.  The
  five lemma `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono'` then concludes.
* Finally, the hypotheses of `solidEquiv_right` live at the targets `iD.obj (N⟦m⟧)` while the
  long exact sequence lives at the targets `(iD.obj N)⟦m⟧`; these differ by the `CommShift`
  isomorphism of `derivedInclusion`, and `bijective_yonMor_iso` transfers bijectivity across
  an isomorphism of targets.
-/

namespace Work.TOOLKIT.Les

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-! ## Yoneda maps -/

/-- The morphism `Hom(Y, C) ⟶ Hom(X, C)` in `AddCommGrpCat` induced by `f : X ⟶ Y`: the
Yoneda image of `fᵒᵖ`.  Its underlying function is precomposition with `f`. -/
def yonMor {X Y : DCat} (f : X ⟶ Y) (C : DCat) :
    (preadditiveYoneda.obj C).obj (Opposite.op Y) ⟶ (preadditiveYoneda.obj C).obj (Opposite.op X) :=
  (preadditiveYoneda.obj C).map (Quiver.Hom.op f)

lemma yonMor_apply {X Y C : DCat} (f : X ⟶ Y) (u : Y ⟶ C) :
    (yonMor f C) u = f ≫ u := rfl

/-- The underlying function of `yonMor f A` is precomposition with `f`. -/
lemma yonMor_fun {X Y A : DCat} (f : X ⟶ Y) :
    (⇑(yonMor f A) : (Y ⟶ A) → (X ⟶ A)) = fun u => f ≫ u := by
  funext u
  exact yonMor_apply f u

lemma isIso_yonMor_of_bijective {X Y A : DCat} (f : X ⟶ Y)
    (hf : Function.Bijective (fun u : Y ⟶ A => f ≫ u)) : IsIso (yonMor f A) := by
  rw [ConcreteCategory.isIso_iff_bijective, yonMor_fun]
  exact hf

lemma isIso_yonMor_iff_bijective {X Y A : DCat} (f : X ⟶ Y) :
    IsIso (yonMor f A) ↔ Function.Bijective (fun u : Y ⟶ A => f ≫ u) := by
  rw [ConcreteCategory.isIso_iff_bijective, yonMor_fun]
  rfl

/-- Precomposition with a fixed morphism, against isomorphic targets: bijectivity is
transported along an isomorphism `A ≅ B` of target objects. -/
lemma bijective_yonMor_iso {X Y A B : DCat} (f : X ⟶ Y) (e : A ≅ B) :
    Function.Bijective (fun u : Y ⟶ A => f ≫ u) ↔
      Function.Bijective (fun u : Y ⟶ B => f ≫ u) := by
  constructor
  · intro h
    refine ⟨fun u v huv => ?_, fun v => ?_⟩
    · have huv' : f ≫ u = f ≫ v := huv
      have h1 : f ≫ (u ≫ e.inv) = f ≫ (v ≫ e.inv) := by
        rw [← Category.assoc, ← Category.assoc, huv']
      have h2 : u ≫ e.inv = v ≫ e.inv := h.1 h1
      have h3 := congrArg (fun t : Y ⟶ A => t ≫ e.hom) h2
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h3
    · obtain ⟨u, hu⟩ := h.2 (v ≫ e.inv)
      have hu' : f ≫ u = v ≫ e.inv := hu
      refine ⟨u ≫ e.hom, ?_⟩
      show f ≫ (u ≫ e.hom) = v
      rw [← Category.assoc, hu', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro h
    refine ⟨fun u v huv => ?_, fun v => ?_⟩
    · have huv' : f ≫ u = f ≫ v := huv
      have h1 : f ≫ (u ≫ e.hom) = f ≫ (v ≫ e.hom) := by
        rw [← Category.assoc, ← Category.assoc, huv']
      have h2 : u ≫ e.hom = v ≫ e.hom := h.1 h1
      have h3 := congrArg (fun t : Y ⟶ B => t ≫ e.inv) h2
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h3
    · obtain ⟨u, hu⟩ := h.2 (v ≫ e.hom)
      have hu' : f ≫ u = v ≫ e.hom := hu
      refine ⟨u ≫ e.inv, ?_⟩
      show f ≫ (u ≫ e.inv) = v
      rw [← Category.assoc, hu', Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ## Two-out-of-three for the long exact sequence

The five lemma applied to the morphism of six-term exact sequences
`Hom(T₂, W⟦n⟧)` and `Hom(T₁, W⟦n⟧)` attached to a morphism of distinguished triangles. -/

set_option maxHeartbeats 1600000 in
/-- Two-out-of-three for a morphism `ψ : T₁ ⟶ T₂` of distinguished triangles, on the
contravariant long exact sequences `Hom(-, W⟦n⟧)`: if precomposition with `ψ.hom₁` and with
`ψ.hom₂` are bijective at the shifts `n₀` and `n₁ = n₀ + 1`, then precomposition with
`ψ.hom₃` is bijective at the shift `n₁`. -/
theorem les_two_of_three {T₁ T₂ : Triangle DCat}
    (h₁ : T₁ ∈ distinguishedTriangles) (h₂ : T₂ ∈ distinguishedTriangles)
    (ψ : T₁ ⟶ T₂) (W : DCat) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (hA₀ : Function.Bijective (fun u : T₂.obj₁ ⟶ W⟦n₀⟧ => ψ.hom₁ ≫ u))
    (hB₀ : Function.Bijective (fun u : T₂.obj₂ ⟶ W⟦n₀⟧ => ψ.hom₂ ≫ u))
    (hB₁ : Function.Bijective (fun u : T₂.obj₂ ⟶ W⟦n₁⟧ => ψ.hom₂ ≫ u))
    (hA₁ : Function.Bijective (fun u : T₂.obj₁ ⟶ W⟦n₁⟧ => ψ.hom₁ ≫ u)) :
    Function.Bijective (fun u : T₂.obj₃ ⟶ W⟦n₁⟧ => ψ.hom₃ ≫ u) := by
  -- the Yoneda functor `Hom(-, W)` on `D(LightCondAb)ᵒᵖ`
  let F : DCatᵒᵖ ⥤ AddCommGrpCat := preadditiveYoneda.obj W
  -- the two triangles, moved to the opposite category
  let Top₁ : Triangle DCatᵒᵖ := opTriangle T₁
  let Top₂ : Triangle DCatᵒᵖ := opTriangle T₂
  have hTop₂ : Top₂ ∈ distinguishedTriangles := op_distinguished T₂ h₂
  have hTop₁ : Top₁ ∈ distinguishedTriangles := op_distinguished T₁ h₁
  -- the morphism of op-triangles induced by `ψ`
  let Φ : Top₂ ⟶ Top₁ := (triangleOpEquivalence DCat).functor.map (Quiver.Hom.op ψ)
  -- the two six-term exact sequences
  let R₂ : ComposableArrows AddCommGrpCat 5 := F.homologySequenceComposableArrows₅ Top₂ n₀ n₁ h
  let R₁ : ComposableArrows AddCommGrpCat 5 := F.homologySequenceComposableArrows₅ Top₁ n₀ n₁ h
  have hR₂ : R₂.Exact := F.homologySequenceComposableArrows₅_exact Top₂ hTop₂ n₀ n₁ h
  have hR₁ : R₁.Exact := F.homologySequenceComposableArrows₅_exact Top₁ hTop₁ n₀ n₁ h
  -- the ladder is a morphism of exact sequences
  have sq0 : R₂.map' 0 1 ≫ (F.shift n₀).map Φ.hom₂ = (F.shift n₀).map Φ.hom₁ ≫ R₁.map' 0 1 := by
    change (F.shift n₀).map Top₂.mor₁ ≫ (F.shift n₀).map Φ.hom₂ =
      (F.shift n₀).map Φ.hom₁ ≫ (F.shift n₀).map Top₁.mor₁
    rw [← Functor.map_comp, ← Functor.map_comp, Φ.comm₁]
  have sq1 : R₂.map' 1 2 ≫ (F.shift n₀).map Φ.hom₃ = (F.shift n₀).map Φ.hom₂ ≫ R₁.map' 1 2 := by
    change (F.shift n₀).map Top₂.mor₂ ≫ (F.shift n₀).map Φ.hom₃ =
      (F.shift n₀).map Φ.hom₂ ≫ (F.shift n₀).map Top₁.mor₂
    rw [← Functor.map_comp, ← Functor.map_comp, Φ.comm₂]
  have sq2 : R₂.map' 2 3 ≫ (F.shift n₁).map Φ.hom₁ = (F.shift n₀).map Φ.hom₃ ≫ R₁.map' 2 3 := by
    change F.homologySequenceδ Top₂ n₀ n₁ h ≫ (F.shift n₁).map Φ.hom₁ =
      (F.shift n₀).map Φ.hom₃ ≫ F.homologySequenceδ Top₁ n₀ n₁ h
    exact (Functor.homologySequenceδ_naturality F Φ n₀ n₁ h).symm
  have sq3 : R₂.map' 3 4 ≫ (F.shift n₁).map Φ.hom₂ = (F.shift n₁).map Φ.hom₁ ≫ R₁.map' 3 4 := by
    change (F.shift n₁).map Top₂.mor₁ ≫ (F.shift n₁).map Φ.hom₂ =
      (F.shift n₁).map Φ.hom₁ ≫ (F.shift n₁).map Top₁.mor₁
    rw [← Functor.map_comp, ← Functor.map_comp, Φ.comm₁]
  have sq4 : R₂.map' 4 5 ≫ (F.shift n₁).map Φ.hom₃ = (F.shift n₁).map Φ.hom₂ ≫ R₁.map' 4 5 := by
    change (F.shift n₁).map Top₂.mor₂ ≫ (F.shift n₁).map Φ.hom₃ =
      (F.shift n₁).map Φ.hom₂ ≫ (F.shift n₁).map Top₁.mor₂
    rw [← Functor.map_comp, ← Functor.map_comp, Φ.comm₂]
  let φ : R₂ ⟶ R₁ := ComposableArrows.homMk₅ ((F.shift n₀).map Φ.hom₁) ((F.shift n₀).map Φ.hom₂)
    ((F.shift n₀).map Φ.hom₃) ((F.shift n₁).map Φ.hom₁) ((F.shift n₁).map Φ.hom₂)
    ((F.shift n₁).map Φ.hom₃) sq0 sq1 sq2 sq3 sq4
  -- the hypotheses of the five lemma, at the first, second, fourth and fifth column
  have hOne : Epi (ComposableArrows.app' φ 1) := by
    have hh : IsIso (yonMor ψ.hom₂ (W⟦n₀⟧)) := isIso_yonMor_of_bijective ψ.hom₂ hB₀
    show Epi (yonMor ψ.hom₂ (W⟦n₀⟧))
    infer_instance
  have hTwo : IsIso (ComposableArrows.app' φ 2) := by
    show IsIso (yonMor ψ.hom₁ (W⟦n₀⟧))
    exact isIso_yonMor_of_bijective ψ.hom₁ hA₀
  have hFour : IsIso (ComposableArrows.app' φ 4) := by
    show IsIso (yonMor ψ.hom₂ (W⟦n₁⟧))
    exact isIso_yonMor_of_bijective ψ.hom₂ hB₁
  have hFive : Mono (ComposableArrows.app' φ 5) := by
    have hh : IsIso (yonMor ψ.hom₁ (W⟦n₁⟧)) := isIso_yonMor_of_bijective ψ.hom₁ hA₁
    show Mono (yonMor ψ.hom₁ (W⟦n₁⟧))
    infer_instance
  -- the five lemma
  have hφ : IsIso (ComposableArrows.app' φ 3) :=
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (k := 1) (by norm_num) hR₂ hR₁ φ 1 2 3 4 5
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hOne hTwo hFour hFive
  have hfin : IsIso (yonMor ψ.hom₃ (W⟦n₁⟧)) := by
    show IsIso (ComposableArrows.app' φ 3)
    exact hφ
  exact (isIso_yonMor_iff_bijective ψ.hom₃).1 hfin

/-! ## The requested statement -/

set_option maxHeartbeats 800000 in
/-- Two-out-of-three for a morphism of distinguished triangles `ψ : T₁ ⟶ T₂` on the contravariant
long exact `Hom(-, iD.obj N⟦m⟧)` sequences: if precomposition with `ψ.hom₁` and with
`ψ.hom₂` are bijective (at every shift `m`), then so is precomposition with `ψ.hom₃` (at `k`). -/
theorem solidEquiv_right {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle Work.TOOLKIT.DCat}
    (h₁ : T₁ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (h₂ : T₂ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (ψ : T₁ ⟶ T₂) (N : Work.TOOLKIT.SDCat)
    (hA : ∀ m : ℤ, Function.Bijective (fun u : T₂.obj₁ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat m).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₁ u))
    (hB : ∀ m : ℤ, Function.Bijective (fun u : T₂.obj₂ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat m).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₂ u))
    (k : ℤ) : Function.Bijective (fun u : T₂.obj₃ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat k).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₃ u) := by
  have hk : (k - 1) + 1 = k := by ring
  -- `iD` commutes with the shift, so `(iD.obj N)⟦m⟧ ≅ iD.obj (N⟦m⟧)`
  have e₀ : (iD.obj N)⟦k - 1⟧ ≅ iD.obj (N⟦k - 1⟧) := ((iD.commShiftIso (k - 1)).app N).symm
  have e₁ : (iD.obj N)⟦k⟧ ≅ iD.obj (N⟦k⟧) := ((iD.commShiftIso k).app N).symm
  -- transport the hypotheses to the targets `(iD.obj N)⟦m⟧`
  have hA₀ : Function.Bijective (fun u : T₂.obj₁ ⟶ (iD.obj N)⟦k - 1⟧ => ψ.hom₁ ≫ u) :=
    (bijective_yonMor_iso ψ.hom₁ e₀).2 (hA (k - 1))
  have hB₀ : Function.Bijective (fun u : T₂.obj₂ ⟶ (iD.obj N)⟦k - 1⟧ => ψ.hom₂ ≫ u) :=
    (bijective_yonMor_iso ψ.hom₂ e₀).2 (hB (k - 1))
  have hB₁ : Function.Bijective (fun u : T₂.obj₂ ⟶ (iD.obj N)⟦k⟧ => ψ.hom₂ ≫ u) :=
    (bijective_yonMor_iso ψ.hom₂ e₁).2 (hB k)
  have hA₁ : Function.Bijective (fun u : T₂.obj₁ ⟶ (iD.obj N)⟦k⟧ => ψ.hom₁ ≫ u) :=
    (bijective_yonMor_iso ψ.hom₁ e₁).2 (hA k)
  exact (bijective_yonMor_iso ψ.hom₃ e₁).1
    (les_two_of_three h₁ h₂ ψ (iD.obj N) (k - 1) k hk hA₀ hB₀ hB₁ hA₁)

end

end Work.TOOLKIT.Les
