import Mathlib
import Submission.Work.RESOL.Basic

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.RESOL

open CategoryTheory.Pretriangulated.Opposite

/-!
# `SolidCofibrantH` is stable under mapping cones

In a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` of `K(LightCondAb)`, if all shifts of
`T₁` and `T₂` are solid-cofibrant, then so is `T₃`.  The proof compares the long exact
sequences of `Hom(-,A)` (in `K`) and of `Hom_D(Qh(-), Qh A)` (in `D`) attached to the
triangle, and applies the five lemma.

Both long exact sequences are computed with the *tautological* shift sequences, so that
the `n`-th term of the `K`-sequence is `Hom_K(X⟦-n⟧, A)` and the `n`-th term of the
`D`-sequence is `Hom_D(Qh(X⟦-n⟧), Qh A)`: the hypotheses of the theorem then match the
comparison maps verbatim, and the compatibility of the two sequences is pure naturality
of `Qh`.
-/

/-- `Hom(-,A)` as a functor on `KCatᵒᵖ`.  It is the covariant Yoneda embedding (for the
opposite category), so that the shift sequence provided by Mathlib is the tautological one. -/
abbrev homKA (A : KCat) : KCatᵒᵖ ⥤ AddCommGrpCat :=
  (preadditiveCoyoneda.obj (Opposite.op (Opposite.op A)) : KCatᵒᵖ ⥤ AddCommGrpCat)

/-- `Hom(-,B)` as a functor on `DCatᵒᵖ`. -/
abbrev homDB (B : DCat) : DCatᵒᵖ ⥤ AddCommGrpCat :=
  (preadditiveCoyoneda.obj (Opposite.op (Opposite.op B)) : DCatᵒᵖ ⥤ AddCommGrpCat)

/-- The composite `Hom_D(Qh(-), Qh A)` as a functor on `KCatᵒᵖ`. -/
abbrev homDA (A : KCat) : KCatᵒᵖ ⥤ AddCommGrpCat :=
  (DerivedCategory.Qh (C := LightCondAb)).op ⋙
    homDB ((DerivedCategory.Qh (C := LightCondAb)).obj A)

/-- The evaluation of the covariant Yoneda embedding on morphisms: it is postcomposition. -/
@[simp] lemma preadditiveCoyoneda_map_apply {C : Type*} [Category C] [Preadditive C] (X : Cᵒᵖ)
    {Y Y' : C} (h : Y ⟶ Y') (u : Opposite.unop X ⟶ Y) :
    ((preadditiveCoyoneda.obj X).map h) u = u ≫ h := by
  simp only [preadditiveCoyoneda, preadditiveCoyonedaObj, Functor.comp_map, ModuleCat.forget₂_map,
    AddCommGrpCat.hom_ofHom, ModuleCat.ofHom, ModuleCat.hom_ofHom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The comparison `Hom_K(-,A) ⟶ Hom_D(Qh(-), Qh A)` induced by the localization functor. -/
def cmpNat (A : KCat) : homKA A ⟶ homDA A where
  app Y := AddCommGrpCat.ofHom
    { toFun := fun u => (DerivedCategory.Qh (C := LightCondAb)).op.map u
      map_zero' := by rw [Functor.map_zero]
      map_add' := fun u v => by rw [Functor.map_add] }
  naturality Y Y' h := by
    set_option backward.isDefEq.respectTransparency false in
    ext u
    show (DerivedCategory.Qh (C := LightCondAb)).op.map (u ≫ h) =
      (DerivedCategory.Qh (C := LightCondAb)).op.map u ≫
        (DerivedCategory.Qh (C := LightCondAb)).op.map h
    rw [Functor.map_comp]

@[simp] lemma cmpNat_app_apply (A : KCat) (Y : KCatᵒᵖ)
    (u : Opposite.unop (Opposite.op (Opposite.op A)) ⟶ Y) :
    (cmpNat A).app Y u = (DerivedCategory.Qh (C := LightCondAb)).op.map u := rfl

/-! ## Moving between `KCat` and `KCatᵒᵖ`

The morphism sets `Hom_K(X,A)` and `Hom_{Kᵒᵖ}(op A, op X)` are canonically identified
(via `Quiver.Hom.op`/`unop`).  We need the resulting transport of bijectivity. -/

/-- `Function.Bijective` is invariant under the canonical identification of `Hom(X,Y)` with
`Hom(op Y, op X)` and of `Hom(Qh X, Qh Y)` with `Hom(op (Qh Y), op (Qh X))`. -/
lemma bijective_op_iff {X Y : KCat}
    (g : (X ⟶ Y) → (DerivedCategory.Qh.obj X ⟶ DerivedCategory.Qh.obj Y)) :
    Function.Bijective (fun u : Opposite.op Y ⟶ Opposite.op X => (g u.unop).op) ↔
      Function.Bijective g := by
  have hop : Function.Bijective
      (fun w : DerivedCategory.Qh.obj X ⟶ DerivedCategory.Qh.obj Y => w.op) :=
    ⟨fun a b h => Quiver.Hom.op_inj h, fun b => ⟨b.unop, Quiver.Hom.op_unop b⟩⟩
  have hunop : Function.Bijective (fun u : Opposite.op Y ⟶ Opposite.op X => u.unop) :=
    ⟨fun a b h => Quiver.Hom.unop_inj h, fun b => ⟨b.op, Quiver.Hom.unop_op b⟩⟩
  have h1 : (fun u : Opposite.op Y ⟶ Opposite.op X => (g u.unop).op) =
      (fun w : DerivedCategory.Qh.obj X ⟶ DerivedCategory.Qh.obj Y => w.op) ∘
        (g ∘ (fun u : Opposite.op Y ⟶ Opposite.op X => u.unop)) := rfl
  rw [h1, Function.Bijective.of_comp_iff' hop]
  exact Function.Bijective.of_comp_iff g hunop

/-- The `op`-form of `SolidCofibrantH`'s bijectivity, for a fixed target. -/
lemma bijective_op_of_bijective {X Y : KCat}
    (h : Function.Bijective (fun f : X ⟶ Y => DerivedCategory.Qh.map f)) :
    Function.Bijective (fun u : Opposite.op Y ⟶ Opposite.op X =>
      (DerivedCategory.Qh (C := LightCondAb)).op.map u) := by
  have h1 : (fun u : Opposite.op Y ⟶ Opposite.op X =>
      (DerivedCategory.Qh (C := LightCondAb)).op.map u) =
      (fun u : Opposite.op Y ⟶ Opposite.op X =>
        ((fun f : X ⟶ Y => DerivedCategory.Qh.map f) u.unop).op) := rfl
  rw [h1]
  exact (bijective_op_iff (fun f : X ⟶ Y => DerivedCategory.Qh.map f)).mpr h

/-- The converse of `bijective_op_of_bijective`. -/
lemma bijective_of_op_bijective {X Y : KCat}
    (h : Function.Bijective (fun u : Opposite.op Y ⟶ Opposite.op X =>
      (DerivedCategory.Qh (C := LightCondAb)).op.map u)) :
    Function.Bijective (fun f : X ⟶ Y => DerivedCategory.Qh.map f) := by
  have h1 : (fun u : Opposite.op Y ⟶ Opposite.op X =>
      (DerivedCategory.Qh (C := LightCondAb)).op.map u) =
      (fun u : Opposite.op Y ⟶ Opposite.op X =>
        ((fun f : X ⟶ Y => DerivedCategory.Qh.map f) u.unop).op) := rfl
  rw [h1] at h
  exact (bijective_op_iff (fun f : X ⟶ Y => DerivedCategory.Qh.map f)).mp h

theorem solidCofibrantH_of_distinguishedTriangle
    (T : CategoryTheory.Pretriangulated.Triangle Work.RESOL.KCat)
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (h₁ : ∀ n : ℤ, Work.RESOL.SolidCofibrantH
      ((CategoryTheory.shiftFunctor Work.RESOL.KCat n).obj T.obj₁))
    (h₂ : ∀ n : ℤ, Work.RESOL.SolidCofibrantH
      ((CategoryTheory.shiftFunctor Work.RESOL.KCat n).obj T.obj₂)) :
    Work.RESOL.SolidCofibrantH T.obj₃ := by
  intro N
  let A : KCat := Submission.Blueprint.hq (Submission.Blueprint.ιC.obj N)
  letI instK : (homKA A).ShiftSequence ℤ := Functor.ShiftSequence.tautological _ _
  letI instD : (homDA A).ShiftSequence ℤ := Functor.ShiftSequence.tautological _ _
  let Top : CategoryTheory.Pretriangulated.Triangle (KCatᵒᵖ) :=
    (CategoryTheory.Pretriangulated.triangleOpEquivalence KCat).functor.obj (Opposite.op T)
  have hTop : Top ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
    CategoryTheory.Pretriangulated.op_distinguished T hT
  have hq : (-1 : ℤ) + 1 = 0 := by norm_num
  let α : homKA A ⟶ homDA A := cmpNat A
  let ψ : ∀ m : ℤ, (homKA A).shift m ⟶ (homDA A).shift m :=
    fun m => Functor.whiskerLeft (shiftFunctor (KCatᵒᵖ) m) α
  let R₁ : ComposableArrows AddCommGrpCat 5 :=
    (homKA A).homologySequenceComposableArrows₅ Top (-1) 0 hq
  let R₂ : ComposableArrows AddCommGrpCat 5 :=
    (homDA A).homologySequenceComposableArrows₅ Top (-1) 0 hq
  have hR₁ : R₁.Exact :=
    (homKA A).homologySequenceComposableArrows₅_exact Top hTop (-1) 0 hq
  have hR₂ : R₂.Exact :=
    (homDA A).homologySequenceComposableArrows₅_exact Top hTop (-1) 0 hq
  -- the two components of the connecting map `Hom(T₁⟦-1⟧) ⟶ Hom(T₃⟦0⟧)`
  let x := Top.mor₃⟦(-1 : ℤ)⟧'
  let y := (shiftFunctorAdd' (KCatᵒᵖ) 1 (-1) 0 (by rw [add_comm 1, hq])).inv.app Top.obj₁
  have keyK : (homKA A).homologySequenceδ Top (-1) 0 hq =
      (homKA A).map x ≫ (homKA A).map y := by
    show ((homKA A).shift (-1)).map Top.mor₃ ≫
      ((homKA A).shiftIso 1 (-1) 0 (by rw [add_comm 1, hq])).hom.app Top.obj₁ = _
    rfl
  have keyD : (homDA A).homologySequenceδ Top (-1) 0 hq =
      (homDA A).map x ≫ (homDA A).map y := by
    show ((homDA A).shift (-1)).map Top.mor₃ ≫
      ((homDA A).shiftIso 1 (-1) 0 (by rw [add_comm 1, hq])).hom.app Top.obj₁ = _
    rfl
  let φ : R₁ ⟶ R₂ := ComposableArrows.homMk₅
    ((ψ (-1)).app Top.obj₁) ((ψ (-1)).app Top.obj₂) ((ψ (-1)).app Top.obj₃)
    ((ψ 0).app Top.obj₁) ((ψ 0).app Top.obj₂) ((ψ 0).app Top.obj₃)
    (by
      show (homKA A).map (Top.mor₁⟦(-1 : ℤ)⟧') ≫
          α.app ((shiftFunctor (KCatᵒᵖ) (-1)).obj Top.obj₂) =
        α.app ((shiftFunctor (KCatᵒᵖ) (-1)).obj Top.obj₁) ≫
          (homDA A).map (Top.mor₁⟦(-1 : ℤ)⟧')
      exact NatTrans.naturality α _)
    (by
      show (homKA A).map (Top.mor₂⟦(-1 : ℤ)⟧') ≫
          α.app ((shiftFunctor (KCatᵒᵖ) (-1)).obj Top.obj₃) =
        α.app ((shiftFunctor (KCatᵒᵖ) (-1)).obj Top.obj₂) ≫
          (homDA A).map (Top.mor₂⟦(-1 : ℤ)⟧')
      exact NatTrans.naturality α _)
    (by
      show ((homKA A).map x ≫ (homKA A).map y) ≫
          α.app ((shiftFunctor (KCatᵒᵖ) (0 : ℤ)).obj Top.obj₁) =
        α.app ((shiftFunctor (KCatᵒᵖ) (-1)).obj Top.obj₃) ≫
          ((homDA A).map x ≫ (homDA A).map y)
      calc ((homKA A).map x ≫ (homKA A).map y) ≫
            α.app ((shiftFunctor (KCatᵒᵖ) (0 : ℤ)).obj Top.obj₁)
          = (homKA A).map (x ≫ y) ≫
              α.app ((shiftFunctor (KCatᵒᵖ) (0 : ℤ)).obj Top.obj₁) := by
            rw [Functor.map_comp]
        _ = α.app ((shiftFunctor (KCatᵒᵖ) (-1)).obj Top.obj₃) ≫
              (homDA A).map (x ≫ y) := NatTrans.naturality α (x ≫ y)
        _ = α.app ((shiftFunctor (KCatᵒᵖ) (-1)).obj Top.obj₃) ≫
              ((homDA A).map x ≫ (homDA A).map y) := by
            rw [Functor.map_comp])
    (by
      show (homKA A).map (Top.mor₁⟦(0 : ℤ)⟧') ≫
          α.app ((shiftFunctor (KCatᵒᵖ) (0 : ℤ)).obj Top.obj₂) =
        α.app ((shiftFunctor (KCatᵒᵖ) (0 : ℤ)).obj Top.obj₁) ≫
          (homDA A).map (Top.mor₁⟦(0 : ℤ)⟧')
      exact NatTrans.naturality α _)
    (by
      show (homKA A).map (Top.mor₂⟦(0 : ℤ)⟧') ≫
          α.app ((shiftFunctor (KCatᵒᵖ) (0 : ℤ)).obj Top.obj₃) =
        α.app ((shiftFunctor (KCatᵒᵖ) (0 : ℤ)).obj Top.obj₂) ≫
          (homDA A).map (Top.mor₂⟦(0 : ℤ)⟧')
      exact NatTrans.naturality α _)
  have h1Epi : Epi (ComposableArrows.app' φ 1) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    show Function.Surjective (fun u : Opposite.op A ⟶ Opposite.op (T.obj₂⟦(1 : ℤ)⟧) =>
      (DerivedCategory.Qh (C := LightCondAb)).op.map u)
    exact (bijective_op_of_bijective (h₂ 1 N)).2
  have h2Iso : IsIso (ComposableArrows.app' φ 2) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    show Function.Bijective (fun u : Opposite.op A ⟶ Opposite.op (T.obj₁⟦(1 : ℤ)⟧) =>
      (DerivedCategory.Qh (C := LightCondAb)).op.map u)
    exact bijective_op_of_bijective (h₁ 1 N)
  have h4Iso : IsIso (ComposableArrows.app' φ 4) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    show Function.Bijective (fun u : Opposite.op A ⟶ Opposite.op (T.obj₂⟦(0 : ℤ)⟧) =>
      (DerivedCategory.Qh (C := LightCondAb)).op.map u)
    exact bijective_op_of_bijective (h₂ 0 N)
  have h5Mono : Mono (ComposableArrows.app' φ 5) := by
    rw [AddCommGrpCat.mono_iff_injective]
    show Function.Injective (fun u : Opposite.op A ⟶ Opposite.op (T.obj₁⟦(0 : ℤ)⟧) =>
      (DerivedCategory.Qh (C := LightCondAb)).op.map u)
    exact (bijective_op_of_bijective (h₁ 0 N)).1
  have hφ : IsIso (ComposableArrows.app' φ 3) :=
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (k := 1) (by norm_num : 1 + 4 ≤ 5)
      hR₁ hR₂ φ 1 2 3 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      h1Epi h2Iso h4Iso h5Mono
  -- A bijection `Hom_K(T₃⟦0⟧, A) ≅ Hom_D(Qh(T₃⟦0⟧), Qh A)`.
  have hM : Function.Bijective (fun w : T.obj₃⟦(0 : ℤ)⟧ ⟶ A =>
      DerivedCategory.Qh.map w) :=
    bijective_of_op_bijective (X := T.obj₃⟦(0 : ℤ)⟧) (Y := A) (by
      show Function.Bijective (fun u : Opposite.op A ⟶ Opposite.op (T.obj₃⟦(0 : ℤ)⟧) =>
        (DerivedCategory.Qh (C := LightCondAb)).op.map u)
      exact (ConcreteCategory.isIso_iff_bijective (ComposableArrows.app' φ 3)).mp hφ)
  -- Transportation along `T₃⟦0⟧ ≅ T₃`.
  let e₀ : T.obj₃⟦(0 : ℤ)⟧ ≅ T.obj₃ := (shiftFunctorZero KCat ℤ).app T.obj₃
  let z' : T.obj₃⟦(0 : ℤ)⟧ ⟶ T.obj₃ := e₀.hom
  let ζ : T.obj₃ ⟶ T.obj₃⟦(0 : ℤ)⟧ := e₀.inv
  have hzζ : z' ≫ ζ = 𝟙 (T.obj₃⟦(0 : ℤ)⟧) := e₀.hom_inv_id
  have hζz : ζ ≫ z' = 𝟙 T.obj₃ := e₀.inv_hom_id
  let e : DerivedCategory.Qh.obj (T.obj₃⟦(0 : ℤ)⟧) ≅ DerivedCategory.Qh.obj T.obj₃ :=
    (DerivedCategory.Qh (C := LightCondAb)).mapIso e₀
  have hmap : DerivedCategory.Qh.map z' = e.hom := rfl
  have hτ : Function.Bijective (fun f : T.obj₃ ⟶ A => z' ≫ f) := by
    refine ⟨fun f₁ f₂ h => ?_, fun g => ⟨ζ ≫ g, ?_⟩⟩
    · have h' := congrArg (fun t => ζ ≫ t) h
      simpa only [← Category.assoc, hζz, Category.id_comp] using h'
    · show z' ≫ (ζ ≫ g) = g
      rw [← Category.assoc, hzζ, Category.id_comp]
  have hρ : Function.Bijective (fun w : DerivedCategory.Qh.obj (T.obj₃⟦(0 : ℤ)⟧) ⟶
      DerivedCategory.Qh.obj A => e.inv ≫ w) := by
    refine ⟨fun w₁ w₂ h => ?_, fun w => ⟨e.hom ≫ w, ?_⟩⟩
    · have h' := congrArg (fun t => e.hom ≫ t) h
      simpa only [← Category.assoc, e.hom_inv_id, Category.id_comp] using h'
    · show e.inv ≫ (e.hom ≫ w) = w
      rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  have heq : (fun f : T.obj₃ ⟶ A => DerivedCategory.Qh.map f) =
      (fun w : DerivedCategory.Qh.obj (T.obj₃⟦(0 : ℤ)⟧) ⟶ DerivedCategory.Qh.obj A =>
          e.inv ≫ w) ∘
        ((fun w : T.obj₃⟦(0 : ℤ)⟧ ⟶ A => DerivedCategory.Qh.map w) ∘
          (fun f : T.obj₃ ⟶ A => z' ≫ f)) := by
    funext f
    show DerivedCategory.Qh.map f = e.inv ≫ DerivedCategory.Qh.map (z' ≫ f)
    rw [Functor.map_comp, hmap, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [heq]
  exact hρ.comp (hM.comp hτ)

end Work.RESOL
