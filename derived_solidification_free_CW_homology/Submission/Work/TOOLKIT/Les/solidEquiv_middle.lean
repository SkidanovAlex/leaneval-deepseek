import Mathlib
import Submission.Work.TOOLKIT.Basic

namespace Work.TOOLKIT.Les

open CategoryTheory Limits
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

open Work.TOOLKIT

/-! ## Bundled (additive) forms of the structural maps

For the two-out-of-three argument we apply the four lemmas of
`Mathlib/Algebra/FiveLemma.lean`, which are stated for bundled additive homomorphisms.
The maps appearing in the contravariant long exact sequence are all additive, and we
provide the bundled versions here. -/

/-- Precomposition with a fixed morphism `f : X ⟶ Y`, as an additive homomorphism. -/
def mid_precompHom {X Y W : DCat} (f : X ⟶ Y) : (Y ⟶ W) →+ (X ⟶ W) where
  toFun u := f ≫ u
  map_zero' := by simp
  map_add' a b := by simp

@[simp]
lemma mid_precompHom_apply {X Y W : DCat} (f : X ⟶ Y) (u : Y ⟶ W) :
    mid_precompHom f u = f ≫ u := rfl

/-- The map `T.mor₂ ≫ -` of the long exact sequence. -/
def mid_pre₂Hom (T : Triangle DCat) (W : DCat) (k : ℤ) :
    (T.obj₃ ⟶ W⟦k⟧) →+ (T.obj₂ ⟶ W⟦k⟧) :=
  mid_precompHom T.mor₂

/-- The map `T.mor₁ ≫ -` of the long exact sequence. -/
def mid_pre₁Hom (T : Triangle DCat) (W : DCat) (k : ℤ) :
    (T.obj₂ ⟶ W⟦k⟧) →+ (T.obj₁ ⟶ W⟦k⟧) :=
  mid_precompHom T.mor₁

/-- The connecting map of the contravariant long exact sequence, as an additive homomorphism. -/
def mid_connHom (T : Triangle DCat) (W : DCat) (k : ℤ) :
    (T.obj₁ ⟶ W⟦k⟧) →+ (T.obj₃ ⟶ W⟦k+1⟧) :=
  ConcreteCategory.hom
    ((preadditiveYoneda.obj W).homologySequenceδ (opTriangle T) k (k + 1) rfl)

@[simp]
lemma mid_pre₂Hom_apply (T : Triangle DCat) (W : DCat) (k : ℤ) (u : T.obj₃ ⟶ W⟦k⟧) :
    mid_pre₂Hom T W k u = pre₂ T W k u := rfl

@[simp]
lemma mid_pre₁Hom_apply (T : Triangle DCat) (W : DCat) (k : ℤ) (u : T.obj₂ ⟶ W⟦k⟧) :
    mid_pre₁Hom T W k u = pre₁ T W k u := rfl

@[simp]
lemma mid_connHom_apply (T : Triangle DCat) (W : DCat) (k : ℤ) (u : T.obj₁ ⟶ W⟦k⟧) :
    mid_connHom T W k u = conn T W k u := rfl

/-! ## Exactness of the contravariant long exact sequence -/

/-- Exactness of the contravariant long exact sequence at `Hom(T.obj₂, W⟦k⟧)`. -/
theorem mid_les_exact_B (T : Triangle DCat) (hT : T ∈ distinguishedTriangles) (W : DCat) (k : ℤ) :
    Function.Exact (pre₂ T W k) (pre₁ T W k) := by
  have h := (preadditiveYoneda.obj W).homologySequence_exact₂ (opTriangle T)
    (CategoryTheory.Pretriangulated.op_distinguished T hT) k
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness of the contravariant long exact sequence at `Hom(T.obj₁, W⟦k⟧)`. -/
theorem mid_les_exact_C (T : Triangle DCat) (hT : T ∈ distinguishedTriangles) (W : DCat) (k : ℤ) :
    Function.Exact (pre₁ T W k) (conn T W k) := by
  have h := (preadditiveYoneda.obj W).homologySequence_exact₃ (opTriangle T)
    (CategoryTheory.Pretriangulated.op_distinguished T hT) k (k + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness of the contravariant long exact sequence at `Hom(T.obj₃, W⟦k+1⟧)`. -/
theorem mid_les_exact_A (T : Triangle DCat) (hT : T ∈ distinguishedTriangles) (W : DCat) (k : ℤ) :
    Function.Exact (conn T W k) (pre₂ T W (k + 1)) := by
  have h := (preadditiveYoneda.obj W).homologySequence_exact₁ (opTriangle T)
    (CategoryTheory.Pretriangulated.op_distinguished T hT) k (k + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-! ## Naturality of the connecting map -/

/-- The connecting homomorphism of the contravariant long exact sequence, made explicit:
it is `T.mor₃` followed by the shift of `x` by `1`. -/
theorem mid_conn_eq_f (T : Triangle DCat) (W : DCat) (k : ℤ) (x : T.obj₁ ⟶ W⟦k⟧) :
    conn T W k x = T.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' DCat k 1 (k + 1) rfl).inv.app W := by
  rw [Work.TOOLKIT.conn]
  exact Pretriangulated.preadditiveYoneda_homologySequenceδ_apply T k (k + 1) rfl x

/-- Naturality of the connecting map under a morphism of distinguished triangles. -/
theorem mid_conn_naturality_apply {T₁ T₂ : Triangle DCat} (ψ : T₁ ⟶ T₂) (W : DCat) (k : ℤ)
    (u : T₂.obj₁ ⟶ W⟦k⟧) :
    conn T₁ W k (ψ.hom₁ ≫ u) = ψ.hom₃ ≫ conn T₂ W k u := by
  rw [mid_conn_eq_f T₁ W k (ψ.hom₁ ≫ u), mid_conn_eq_f T₂ W k u, Functor.map_comp]
  simp only [← Category.assoc]
  rw [← ψ.comm₃]

/-! ## Shifting the connecting map so that its target matches a fixed degree -/

/-- Postcomposition with an isomorphism, as an additive equivalence. -/
def mid_postcompAddEquiv (X : DCat) {Y Z : DCat} (e : Y ≅ Z) : (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun u := u ≫ e.hom
  invFun u := u ≫ e.inv
  left_inv u := by simp [Category.assoc]
  right_inv u := by simp [Category.assoc]
  map_add' a b := by simp [Preadditive.add_comp]

/-- The canonical isomorphism `W⟦a⟧ ≅ W⟦b⟧` induced by an equality of the shifts. -/
def mid_shiftIsoEq (W : DCat) {a b : ℤ} (h : a = b) : W⟦a⟧ ≅ W⟦b⟧ :=
  eqToIso (congrArg (fun n : ℤ => (shiftFunctor DCat n).obj W) h)

/-- The shift identification sending the target `W⟦k-1+1⟧` of the connecting map at degree `k-1`
to the target `W⟦k⟧` of the degree `k` part of the long exact sequence. -/
def mid_shiftIsoSucc (W : DCat) (k : ℤ) : W⟦k - 1 + 1⟧ ≅ W⟦k⟧ :=
  mid_shiftIsoEq W (by omega)

/-- The connecting map of degree `k-1`, with its target identified with `W⟦k⟧` so that it
precedes `pre₂ T W k` in the exact sequence. -/
def mid_deltaHom (T : Triangle DCat) (W : DCat) (k : ℤ) :
    (T.obj₁ ⟶ W⟦k - 1⟧) →+ (T.obj₃ ⟶ W⟦k⟧) :=
  (mid_postcompAddEquiv (T.obj₃) (mid_shiftIsoSucc W k)).toAddMonoidHom.comp (mid_connHom T W (k - 1))

@[simp]
lemma mid_deltaHom_apply (T : Triangle DCat) (W : DCat) (k : ℤ) (c : T.obj₁ ⟶ W⟦k - 1⟧) :
    mid_deltaHom T W k c = conn T W (k - 1) c ≫ (mid_shiftIsoSucc W k).hom := rfl

lemma mid_pre₂_delta_conj (T : Triangle DCat) (W : DCat) (k : ℤ) (a : T.obj₃ ⟶ W⟦k⟧) :
    pre₂ T W k a = (pre₂ T W (k - 1 + 1) (a ≫ (mid_shiftIsoSucc W k).inv)) ≫ (mid_shiftIsoSucc W k).hom := by
  simp [pre₂, Category.assoc]

/-- Exactness at `Hom(T.obj₃, W⟦k⟧)` with the connecting map of degree `k-1` shifted. -/
theorem mid_exact_delta (T : Triangle DCat) (hT : T ∈ distinguishedTriangles) (W : DCat) (k : ℤ) :
    Function.Exact (mid_deltaHom T W k) (mid_pre₂Hom T W k) := by
  have h := mid_les_exact_A T hT W (k - 1)
  intro a
  change pre₂ T W k a = 0 ↔ a ∈ Set.range ⇑(mid_deltaHom T W k)
  rw [mid_pre₂_delta_conj T W k a]
  constructor
  · intro ha
    have h4 := congrArg (fun t => t ≫ (mid_shiftIsoSucc W k).inv) ha
    have h2 : pre₂ T W (k - 1 + 1) (a ≫ (mid_shiftIsoSucc W k).inv) = 0 := by
      simpa [Category.assoc] using h4
    obtain ⟨c, hc⟩ := (h (a ≫ (mid_shiftIsoSucc W k).inv)).mp h2
    refine ⟨c, ?_⟩
    change conn T W (k - 1) c ≫ (mid_shiftIsoSucc W k).hom = a
    rw [hc]
    simp [Category.assoc]
  · rintro ⟨c, hc⟩
    have h5 : a ≫ (mid_shiftIsoSucc W k).inv = conn T W (k - 1) c := by
      rw [← hc]
      simp [Category.assoc]
    rw [h5, (h (conn T W (k - 1) c)).mpr ⟨c, rfl⟩]
    simp

/-- Naturality of the shifted connecting map. -/
theorem mid_delta_naturality {T₁ T₂ : Triangle DCat} (ψ : T₁ ⟶ T₂) (W : DCat) (k : ℤ) :
    (mid_deltaHom T₁ W k).comp (mid_precompHom (W := W⟦k - 1⟧) ψ.hom₁) =
      (mid_precompHom (W := W⟦k⟧) ψ.hom₃).comp (mid_deltaHom T₂ W k) := by
  ext u
  simp only [AddMonoidHom.comp_apply, mid_deltaHom_apply, mid_precompHom_apply]
  rw [mid_conn_naturality_apply ψ W (k - 1) u]
  simp [Category.assoc]

/-! ## Transporting bijectivity along an isomorphism of the target -/

/-- Precomposition with `f`, into two isormorphic targets, is bijective simultaneously. -/
theorem mid_bijective_precomp_iff_of_iso {X₁ X₂ Y Z : DCat} (f : X₁ ⟶ X₂) (e : Y ≅ Z) :
    Function.Bijective (fun u : X₂ ⟶ Y => f ≫ u) ↔
      Function.Bijective (fun u : X₂ ⟶ Z => f ≫ u) := by
  constructor
  · intro hY
    have h : Function.Bijective (⇑(mid_postcompAddEquiv X₁ e) ∘
        (fun u : X₂ ⟶ Y => f ≫ u) ∘ ⇑(mid_postcompAddEquiv X₂ e).symm) :=
      (mid_postcompAddEquiv X₁ e).bijective.comp (hY.comp (mid_postcompAddEquiv X₂ e).symm.bijective)
    convert h using 1
    funext u
    simp [mid_postcompAddEquiv, Category.assoc]
  · intro hZ
    have h : Function.Bijective (⇑(mid_postcompAddEquiv X₁ e).symm ∘
        (fun u : X₂ ⟶ Z => f ≫ u) ∘ ⇑(mid_postcompAddEquiv X₂ e)) :=
      (mid_postcompAddEquiv X₁ e).symm.bijective.comp (hZ.comp (mid_postcompAddEquiv X₂ e).bijective)
    convert h using 1
    funext u
    simp [mid_postcompAddEquiv, Category.assoc]

/-! ## Two-out-of-three for the middle term

We now prove the requested lemma.  All the diagram chasing is delegated to the four and
five lemmas of `Mathlib/Algebra/FiveLemma.lean`, applied to the two windows

* `A(T₂)ₖ → B(T₂)ₖ → C(T₂)ₖ → A(T₂)ₖ₊₁` (surjectivity of the middle vertical), where
  `A(T)ₖ = Hom(T.obj₃, W⟦k⟧)`, `B(T)ₖ = Hom(T.obj₂, W⟦k⟧)`, `C(T)ₖ = Hom(T.obj₁, W⟦k⟧)`;
* `C(T₂)ₖ₋₁ → A(T₂)ₖ → B(T₂)ₖ → C(T₂)ₖ` (injectivity of the middle vertical).

Note that the middle vertical `β` is the map whose bijectivity is asked for, and the outer
verticals `γ`, `α` are precomposition with `ψ.hom₃`, `ψ.hom₁`.  The only place where the
shift bookkeeping is not automatic is the connecting map at degree `k-1`, whose target
`W⟦k-1+1⟧` has to be identified with `W⟦k⟧`: this is `mid_deltaHom` / `mid_exact_delta` above.
-/
/-- Two-out-of-three for a morphism of distinguished triangles `ψ : T₁ ⟶ T₂` on the contravariant
long exact `Hom(-, iD.obj N⟦m⟧)` sequences: if precomposition with `ψ.hom₁` and with
`ψ.hom₃` are bijective (at every shift `m`), then so is precomposition with `ψ.hom₂` (at
`k`).  A `Bijective` map here is `fun u => ψ.homᵢ ≫ u` between the stated `Hom` types. -/
theorem solidEquiv_middle {T₁ T₂ : CategoryTheory.Pretriangulated.Triangle Work.TOOLKIT.DCat}
    (h₁ : T₁ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (h₂ : T₂ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (ψ : T₁ ⟶ T₂) (N : Work.TOOLKIT.SDCat)
    (hA : ∀ m : ℤ, Function.Bijective (fun u : T₂.obj₁ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat m).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₁ u))
    (hC : ∀ m : ℤ, Function.Bijective (fun u : T₂.obj₃ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat m).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₃ u))
    (k : ℤ) : Function.Bijective (fun u : T₂.obj₂ ⟶
        LightCondensed.Solid.derivedInclusion.obj ((CategoryTheory.shiftFunctor Work.TOOLKIT.SDCat k).obj N) =>
        CategoryTheory.CategoryStruct.comp ψ.hom₂ u) := by
  let W : DCat := iD.obj N
  -- the shift isomorphisms `iD.obj (N⟦m⟧) ≅ (iD.obj N)⟦m⟧`
  have eiso : ∀ m : ℤ, iD.obj ((shiftFunctor SDCat m).obj N) ≅ W⟦m⟧ :=
    fun m => (iD.commShiftIso m).app N
  have hA' : ∀ m : ℤ, Function.Bijective (fun u : T₂.obj₁ ⟶ W⟦m⟧ => ψ.hom₁ ≫ u) := fun m =>
    (mid_bijective_precomp_iff_of_iso (X₁ := T₁.obj₁) (X₂ := T₂.obj₁) ψ.hom₁ (eiso m)).mp (hA m)
  have hC' : ∀ m : ℤ, Function.Bijective (fun u : T₂.obj₃ ⟶ W⟦m⟧ => ψ.hom₃ ≫ u) := fun m =>
    (mid_bijective_precomp_iff_of_iso (X₁ := T₁.obj₃) (X₂ := T₂.obj₃) ψ.hom₃ (eiso m)).mp (hC m)
  -- the two commuting squares of the morphism `ψ` at degree `k`
  have sq₂ : (mid_pre₂Hom T₁ W k).comp (mid_precompHom (W := W⟦k⟧) ψ.hom₃) =
      (mid_precompHom (W := W⟦k⟧) ψ.hom₂).comp (mid_pre₂Hom T₂ W k) := by
    ext x
    simp only [AddMonoidHom.comp_apply, mid_pre₂Hom_apply, mid_precompHom_apply, pre₂]
    simp only [← Category.assoc]
    rw [ψ.comm₂]
  have sq₁ : (mid_pre₁Hom T₁ W k).comp (mid_precompHom (W := W⟦k⟧) ψ.hom₂) =
      (mid_precompHom (W := W⟦k⟧) ψ.hom₁).comp (mid_pre₁Hom T₂ W k) := by
    ext x
    simp only [AddMonoidHom.comp_apply, mid_pre₁Hom_apply, mid_precompHom_apply, pre₁]
    simp only [← Category.assoc]
    rw [ψ.comm₁]
  have sqδ : (mid_connHom T₁ W k).comp (mid_precompHom (W := W⟦k⟧) ψ.hom₁) =
      (mid_precompHom (W := W⟦k+1⟧) ψ.hom₃).comp (mid_connHom T₂ W k) := by
    ext x
    simp only [AddMonoidHom.comp_apply, mid_connHom_apply, mid_precompHom_apply]
    exact mid_conn_naturality_apply ψ W k x
  have hsurj : Function.Surjective (mid_precompHom (W := W⟦k⟧) ψ.hom₂ :
      (T₂.obj₂ ⟶ W⟦k⟧) → (T₁.obj₂ ⟶ W⟦k⟧)) :=
    AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
      (f₁ := mid_pre₂Hom T₂ W k) (f₂ := mid_pre₁Hom T₂ W k) (f₃ := mid_connHom T₂ W k)
      (g₁ := mid_pre₂Hom T₁ W k) (g₂ := mid_pre₁Hom T₁ W k) (g₃ := mid_connHom T₁ W k)
      (i₁ := mid_precompHom (W := W⟦k⟧) ψ.hom₃)
      (i₂ := mid_precompHom (W := W⟦k⟧) ψ.hom₂)
      (i₃ := mid_precompHom (W := W⟦k⟧) ψ.hom₁)
      (i₄ := mid_precompHom (W := W⟦k+1⟧) ψ.hom₃)
      (hc₁ := sq₂) (hc₂ := sq₁) (hc₃ := sqδ)
      (hf₂ := mid_les_exact_C T₂ h₂ W k) (hg₁ := mid_les_exact_B T₁ h₁ W k)
      (hg₂ := mid_les_exact_C T₁ h₁ W k)
      (hi₁ := (hC' k).2) (hi₃ := (hA' k).2) (hi₄ := (hC' (k + 1)).1)
  have hinj : Function.Injective (mid_precompHom (W := W⟦k⟧) ψ.hom₂ :
      (T₂.obj₂ ⟶ W⟦k⟧) → (T₁.obj₂ ⟶ W⟦k⟧)) :=
    AddMonoidHom.injective_of_surjective_of_injective_of_injective
      (f₁ := mid_deltaHom T₂ W k) (f₂ := mid_pre₂Hom T₂ W k) (f₃ := mid_pre₁Hom T₂ W k)
      (g₁ := mid_deltaHom T₁ W k) (g₂ := mid_pre₂Hom T₁ W k) (g₃ := mid_pre₁Hom T₁ W k)
      (i₁ := mid_precompHom (W := W⟦k-1⟧) ψ.hom₁)
      (i₂ := mid_precompHom (W := W⟦k⟧) ψ.hom₃)
      (i₃ := mid_precompHom (W := W⟦k⟧) ψ.hom₂)
      (i₄ := mid_precompHom (W := W⟦k⟧) ψ.hom₁)
      (hc₁ := mid_delta_naturality ψ W k) (hc₂ := sq₂) (hc₃ := sq₁)
      (hf₁ := mid_exact_delta T₂ h₂ W k) (hf₂ := mid_les_exact_B T₂ h₂ W k)
      (hg₁ := mid_exact_delta T₁ h₁ W k)
      (hi₁ := (hA' (k - 1)).2) (hi₂ := (hC' k).1) (hi₄ := (hA' k).1)
  have hmid : Function.Bijective (fun u : T₂.obj₂ ⟶ W⟦k⟧ => ψ.hom₂ ≫ u) :=
    ⟨hinj, hsurj⟩
  exact (mid_bijective_precomp_iff_of_iso (X₁ := T₁.obj₂) (X₂ := T₂.obj₂) ψ.hom₂ (eiso k)).mpr hmid

end

end Work.TOOLKIT.Les
