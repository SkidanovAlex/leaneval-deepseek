import Mathlib
import Submission.Work.TOOLKIT.Basic

namespace Work.TOOLKIT.Les

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open scoped CategoryTheory.Pretriangulated.Opposite

noncomputable section

/-!
# Two-out-of-three on the contravariant long exact `Hom(-, ι_D N⟦·⟧)` sequences

This file proves `solidEquiv_left`: for a morphism of distinguished triangles `ψ : T₁ ⟶ T₂` in
`D(LightCondAb)`, if precomposition with `ψ.hom₂` and precomposition with `ψ.hom₃` are bijective
on the `Hom(-, ι_D N⟦m⟧)` sequences (for all `m`), then so is precomposition with `ψ.hom₁`
(in the degree under consideration).

The proof is the five lemma applied to the two long exact sequences

`Hom(T.obj₃, W⟦k⟧) → Hom(T.obj₂, W⟦k⟧) → Hom(T.obj₁, W⟦k⟧) → Hom(T.obj₃, W⟦k+1⟧) → Hom(T.obj₂, W⟦k+1⟧)`

for `T = T₁, T₂`, where `W = ι_D N`; the exactness and the naturality of the connecting map
`conn` are proved here from Mathlib's long exact sequence of a homological functor applied to the
opposite triangle `opTriangle T`.  Finally the target `(ι_D N)⟦k⟧` is compared with `ι_D (N⟦k⟧)`
using the commutation isomorphism of `ι_D` with the shifts.

The file is self-contained: everything it needs about the contravariant long exact sequence is
proved in the auxiliary namespace `Work.TOOLKIT.Les.Aux` below (three-term exactness of
`pre₂`, `pre₁`, `conn`, and the naturality of all of them under a morphism of triangles), so
other files may reuse e.g. `Aux.exact_pre₂_pre₁`, `Aux.conn_square`, `Aux.precompHom` and
`Aux.five_lemma_bijective_aux` directly.
-/

/-! The auxiliary lemmas below are kept in a namespace of their own so that they cannot clash
with auxiliary lemmas of other files in the `Work.TOOLKIT.Les` namespace. -/
namespace Aux

/-! ## Transport of bijectivity along an isomorphism of the target -/

/-- Precomposition with a fixed morphism `f` is bijective for the target `W` if and only if it is
bijective for any target isomorphic to `W`. -/
lemma precomp_bijective_iff_of_iso {C : Type*} [Category C] {X Y W W' : C} (f : X ⟶ Y)
    (e : W ≅ W') :
    Function.Bijective (precomp f W) ↔ Function.Bijective (precomp f W') := by
  have hY : Function.Bijective (fun g : Y ⟶ W => g ≫ e.hom) := by
    refine ⟨fun a b hab => ?_, fun g => ⟨g ≫ e.inv, ?_⟩⟩
    · have h := congrArg (fun g : Y ⟶ W' => g ≫ e.inv) hab
      simpa using h
    · simp
  have hX : Function.Bijective (fun g : X ⟶ W => g ≫ e.hom) := by
    refine ⟨fun a b hab => ?_, fun g => ⟨g ≫ e.inv, ?_⟩⟩
    · have h := congrArg (fun g : X ⟶ W' => g ≫ e.inv) hab
      simpa using h
    · simp
  have hcomm : precomp f W' ∘ (fun g : Y ⟶ W => g ≫ e.hom) =
      (fun g : X ⟶ W => g ≫ e.hom) ∘ precomp f W := by
    funext g
    simp only [Function.comp_apply, precomp_apply, Category.assoc]
  constructor
  · intro hf
    have h1 : Function.Bijective ((fun g : X ⟶ W => g ≫ e.hom) ∘ precomp f W) :=
      (Function.Bijective.of_comp_iff' hX (precomp f W)).mpr hf
    rw [← hcomm] at h1
    exact (Function.Bijective.of_comp_iff (precomp f W') hY).mp h1
  · intro hf
    have h1 : Function.Bijective (precomp f W' ∘ (fun g : Y ⟶ W => g ≫ e.hom)) :=
      (Function.Bijective.of_comp_iff (precomp f W') hY).mpr hf
    rw [hcomm] at h1
    exact (Function.Bijective.of_comp_iff' hX (precomp f W)).mp h1

/-! ## Exactness and naturality of the contravariant long exact sequence -/

/-- The opposite of a triangle is a triangle. -/
lemma opTriangle_mem_distinguished {T : CategoryTheory.Pretriangulated.Triangle DCat}
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles) :
    opTriangle T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
  (Pretriangulated.Opposite.mem_distinguishedTriangles_iff' (opTriangle T)).mpr
    ⟨T, hT, ⟨Iso.refl _⟩⟩

/-- Exactness of the contravariant long exact sequence for `Hom(-, W⟦k⟧)` at `Hom(T.obj₂, W⟦k⟧)`:
the kernel of `pre₁` is the image of `pre₂`. -/
lemma exact_pre₂_pre₁ (T : CategoryTheory.Pretriangulated.Triangle DCat)
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles) (W : DCat) (k : ℤ) :
    Function.Exact (pre₂ T W k) (pre₁ T W k) := by
  have h := (preadditiveYoneda.obj W).homologySequence_exact₂ (opTriangle T)
    (opTriangle_mem_distinguished hT) k
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness of the contravariant long exact sequence for `Hom(-, W⟦k⟧)` at `Hom(T.obj₁, W⟦k⟧)`:
the kernel of the connecting map `conn` is the image of `pre₁`. -/
lemma exact_pre₁_conn (T : CategoryTheory.Pretriangulated.Triangle DCat)
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles) (W : DCat) (k : ℤ) :
    Function.Exact (pre₁ T W k) (conn T W k) := by
  have h := (preadditiveYoneda.obj W).homologySequence_exact₃ (opTriangle T)
    (opTriangle_mem_distinguished hT) k (k+1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness of the contravariant long exact sequence for `Hom(-, W⟦k⟧)` at `Hom(T.obj₃, W⟦k+1⟧)`:
the kernel of `pre₂` (at the shift `k+1`) is the image of the connecting map `conn`. -/
lemma exact_conn_pre₂ (T : CategoryTheory.Pretriangulated.Triangle DCat)
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles) (W : DCat) (k : ℤ) :
    Function.Exact (conn T W k) (pre₂ T W (k+1)) := by
  have h := (preadditiveYoneda.obj W).homologySequence_exact₁ (opTriangle T)
    (opTriangle_mem_distinguished hT) k (k+1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- The explicit formula for the connecting homomorphism `conn`, from Mathlib's computation of
`homologySequenceδ` for the Yoneda functor. -/
lemma conn_apply (T : CategoryTheory.Pretriangulated.Triangle DCat) (W : DCat) (k : ℤ)
    (x : T.obj₁ ⟶ (shiftFunctor DCat k).obj W) :
    conn T W k x = T.mor₃ ≫ (shiftFunctor DCat (1 : ℤ)).map x ≫
      (shiftFunctorAdd' DCat k 1 (k+1) rfl).inv.app W :=
  Pretriangulated.preadditiveYoneda_homologySequenceδ_apply T k (k+1) rfl x

/-- Naturality of `conn` under a morphism of distinguished triangles `ψ : T₁ ⟶ T₂`. -/
lemma conn_square {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle DCat} (ψ : T₁ ⟶ T₂)
    (W : DCat) (k : ℤ) (u : T₂.obj₁ ⟶ (shiftFunctor DCat k).obj W) :
    conn T₁ W k (ψ.hom₁ ≫ u) = ψ.hom₃ ≫ conn T₂ W k u := by
  have key : T₁.mor₃ ≫ (shiftFunctor DCat (1 : ℤ)).map ψ.hom₁ = ψ.hom₃ ≫ T₂.mor₃ := ψ.comm₃
  rw [conn_apply, conn_apply, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, key, Category.assoc]

/-- Naturality of `pre₁` under a morphism of distinguished triangles `ψ : T₁ ⟶ T₂`. -/
lemma pre₁_square {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle DCat} (ψ : T₁ ⟶ T₂)
    (W : DCat) (k : ℤ) (u : T₂.obj₂ ⟶ (shiftFunctor DCat k).obj W) :
    pre₁ T₁ W k (ψ.hom₂ ≫ u) = ψ.hom₁ ≫ pre₁ T₂ W k u := by
  calc pre₁ T₁ W k (ψ.hom₂ ≫ u) = T₁.mor₁ ≫ (ψ.hom₂ ≫ u) := rfl
    _ = (T₁.mor₁ ≫ ψ.hom₂) ≫ u := (Category.assoc _ _ _).symm
    _ = (ψ.hom₁ ≫ T₂.mor₁) ≫ u := by rw [ψ.comm₁]
    _ = ψ.hom₁ ≫ (T₂.mor₁ ≫ u) := Category.assoc _ _ _
    _ = ψ.hom₁ ≫ pre₁ T₂ W k u := rfl

/-- Naturality of `pre₂` under a morphism of distinguished triangles `ψ : T₁ ⟶ T₂`. -/
lemma pre₂_square {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle DCat} (ψ : T₁ ⟶ T₂)
    (W : DCat) (k : ℤ) (u : T₂.obj₃ ⟶ (shiftFunctor DCat k).obj W) :
    pre₂ T₁ W k (ψ.hom₃ ≫ u) = ψ.hom₂ ≫ pre₂ T₂ W k u := by
  calc pre₂ T₁ W k (ψ.hom₃ ≫ u) = T₁.mor₂ ≫ (ψ.hom₃ ≫ u) := rfl
    _ = (T₁.mor₂ ≫ ψ.hom₃) ≫ u := (Category.assoc _ _ _).symm
    _ = (ψ.hom₂ ≫ T₂.mor₂) ≫ u := by rw [ψ.comm₂]
    _ = ψ.hom₂ ≫ (T₂.mor₂ ≫ u) := Category.assoc _ _ _
    _ = ψ.hom₂ ≫ pre₂ T₂ W k u := rfl

/-! ## The three maps as additive maps -/

/-- Precomposition with a fixed morphism, as an additive map. -/
noncomputable def precompHom {X Y : DCat} (f : X ⟶ Y) (Z : DCat) : (Y ⟶ Z) →+ (X ⟶ Z) where
  toFun := precomp f Z
  map_zero' := by simp only [precomp_apply, comp_zero]
  map_add' := by intro a b; exact Preadditive.comp_add X Y Z f a b

/-- `pre₁` as an additive map. -/
noncomputable def pre₁Hom (T : CategoryTheory.Pretriangulated.Triangle DCat) (W : DCat) (k : ℤ) :
    (T.obj₂ ⟶ (shiftFunctor DCat k).obj W) →+ (T.obj₁ ⟶ (shiftFunctor DCat k).obj W) :=
  precompHom T.mor₁ ((shiftFunctor DCat k).obj W)

/-- `pre₂` as an additive map. -/
noncomputable def pre₂Hom (T : CategoryTheory.Pretriangulated.Triangle DCat) (W : DCat) (k : ℤ) :
    (T.obj₃ ⟶ (shiftFunctor DCat k).obj W) →+ (T.obj₂ ⟶ (shiftFunctor DCat k).obj W) :=
  precompHom T.mor₂ ((shiftFunctor DCat k).obj W)

/-- The connecting homomorphism `conn` as an additive map. -/
noncomputable def connHom (T : CategoryTheory.Pretriangulated.Triangle DCat) (W : DCat) (k : ℤ) :
    (T.obj₁ ⟶ (shiftFunctor DCat k).obj W) →+ (T.obj₃ ⟶ (shiftFunctor DCat (k+1)).obj W) where
  toFun := conn T W k
  map_zero' := by
    rw [conn_apply]
    simp
  map_add' := by
    intro x y
    rw [conn_apply, conn_apply, conn_apply, Functor.map_add]
    simp only [Preadditive.add_comp, Preadditive.comp_add]

/-! ## The five lemma -/

/-- Five lemma for a map of exact sequences of abelian groups, in the precise shape needed for
`SolidEquiv`: if the maps `i₂`, `i₄` are bijective, `i₁` is surjective and `i₅` is injective, then
`i₃` is bijective. -/
lemma five_lemma_bijective_aux
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type*}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅]
    [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃] [AddCommGroup B₄] [AddCommGroup B₅]
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅)
    (g₁ : B₁ →+ B₂) (g₂ : B₂ →+ B₃) (g₃ : B₃ →+ B₄) (g₄ : B₄ →+ B₅)
    (i₁ : A₁ →+ B₁) (i₂ : A₂ →+ B₂) (i₃ : A₃ →+ B₃) (i₄ : A₄ →+ B₄) (i₅ : A₅ →+ B₅)
    (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
    (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)
    (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
    (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)
    (hi₁ : Function.Surjective i₁) (hi₂ : Function.Bijective i₂)
    (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ :=
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ i₁ i₂ i₃ i₄ i₅
    hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hi₁ hi₂ hi₄ hi₅

end Aux

open Aux

/-! ## The main theorem -/

/-- Two-out-of-three for a morphism of distinguished triangles `ψ : T₁ ⟶ T₂` on the contravariant
long exact `Hom(-, iD.obj N⟦m⟧)` sequences: if precomposition with `ψ.hom₂` and with
`ψ.hom₃` are bijective (at every shift `m`), then so is precomposition with `ψ.hom₁` (at `k`). -/
theorem solidEquiv_left {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle Work.TOOLKIT.DCat}
    (h₁ : T₁ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (h₂ : T₂ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (ψ : T₁ ⟶ T₂) (N : Work.TOOLKIT.SDCat)
    (hB : ∀ m : ℤ, Function.Bijective (fun u : T₂.obj₂ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat m).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₂ u))
    (hC : ∀ m : ℤ, Function.Bijective (fun u : T₂.obj₃ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat m).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₃ u))
    (k : ℤ) : Function.Bijective (fun u : T₂.obj₁ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat k).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₁ u) := by
  -- Rewrite the hypotheses with the target `(ι_D N)⟦m⟧` instead of `ι_D (N⟦m⟧)`.
  have hB' : ∀ m : ℤ, Function.Bijective
      (fun u : T₂.obj₂ ⟶ (shiftFunctor DCat m).obj (iD.obj N) => ψ.hom₂ ≫ u) :=
    fun m => (precomp_bijective_iff_of_iso ψ.hom₂ ((iD.commShiftIso m).app N)).mp (hB m)
  have hC' : ∀ m : ℤ, Function.Bijective
      (fun u : T₂.obj₃ ⟶ (shiftFunctor DCat m).obj (iD.obj N) => ψ.hom₃ ≫ u) :=
    fun m => (precomp_bijective_iff_of_iso ψ.hom₃ ((iD.commShiftIso m).app N)).mp (hC m)
  -- The five lemma applied to the two long exact sequences.
  have key : Function.Bijective
      (fun u : T₂.obj₁ ⟶ (shiftFunctor DCat k).obj (iD.obj N) => ψ.hom₁ ≫ u) :=
    five_lemma_bijective_aux
      (pre₂Hom T₂ (iD.obj N) k) (pre₁Hom T₂ (iD.obj N) k) (connHom T₂ (iD.obj N) k)
      (pre₂Hom T₂ (iD.obj N) (k+1))
      (pre₂Hom T₁ (iD.obj N) k) (pre₁Hom T₁ (iD.obj N) k) (connHom T₁ (iD.obj N) k)
      (pre₂Hom T₁ (iD.obj N) (k+1))
      (precompHom ψ.hom₃ ((shiftFunctor DCat k).obj (iD.obj N)))
      (precompHom ψ.hom₂ ((shiftFunctor DCat k).obj (iD.obj N)))
      (precompHom ψ.hom₁ ((shiftFunctor DCat k).obj (iD.obj N)))
      (precompHom ψ.hom₃ ((shiftFunctor DCat (k+1)).obj (iD.obj N)))
      (precompHom ψ.hom₂ ((shiftFunctor DCat (k+1)).obj (iD.obj N)))
      (by ext x; exact pre₂_square ψ (iD.obj N) k x)
      (by ext x; exact pre₁_square ψ (iD.obj N) k x)
      (by ext x; exact conn_square ψ (iD.obj N) k x)
      (by ext x; exact pre₂_square ψ (iD.obj N) (k+1) x)
      (exact_pre₂_pre₁ T₂ h₂ (iD.obj N) k) (exact_pre₁_conn T₂ h₂ (iD.obj N) k)
      (exact_conn_pre₂ T₂ h₂ (iD.obj N) k)
      (exact_pre₂_pre₁ T₁ h₁ (iD.obj N) k) (exact_pre₁_conn T₁ h₁ (iD.obj N) k)
      (exact_conn_pre₂ T₁ h₁ (iD.obj N) k)
      (hC' k).2 (hB' k) (hC' (k+1)) (hB' (k+1)).1
  exact (precomp_bijective_iff_of_iso ψ.hom₁ ((iD.commShiftIso k).app N)).mpr key

end

end Work.TOOLKIT.Les
