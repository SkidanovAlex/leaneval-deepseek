import Mathlib
import Submission.Work.DISC.Defs
import Submission.Work.DISC.homFreeEquiv_naturality
import Submission.Work.DISC.freeTensorIso_natural
import Submission.Work.REFL.pre_app_points

/-!
# AREA DISC — the sections of `(ΔM)^P` are vanishing locally constant functions

For a discrete abelian group `ΔM` and a light profinite set `S`, the `S`-points of the internal
hom `(ΔM)^P` (where `P = ℤ[ℕ∪{∞}]/ℤ[∞]`) are the locally constant functions on `S × (ℕ∪{∞})`
which vanish on the slice `S × {∞}`, and `(1 - shift)^*` acts on them by the shift-difference
`f ↦ f - f ∘ (id × shift)`.

The chain of identifications is

`(P ⟹ ΔM)(S) ≅ Hom(P ⊗ ℤ[S], ΔM) ≅ Hom(ℤ[S] ⊗ P, ΔM) ≅ Hom(P, ℤ[S] ⟹ ΔM)`

(the closed structure of `LightCondAb`, then the braiding, then currying), followed by the
cokernel presentation `P = coker(ℤ[∞] → ℤ[ℕ∪{∞}])`:

`Hom(P, ℤ[S] ⟹ ΔM) ≅ {g : ℤ[ℕ∪{∞}] ⟶ ℤ[S] ⟹ ΔM // P_map ≫ g = 0}`,

and finally the section-wise identification `(ℤ[S] ⟹ ΔM)(T) ≅ C(S × T, M)` obtained from
`ihomPoints`, the monoidality of `ℤ[-]` and `Hom(ℤ[T], A) ≅ A(T)`.

Everything is done first for the (isomorphic) locally constant model `ΔM^lc` of `ΔM`, whose
sections are *definitionally* locally constant functions, and then transported across
`ΔM^lc ≅ ΔM` using `MonoidalClosed.pre_comm_ihom_map`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.DISC

/-! ## Elementary utility lemmas -/

/-- The functor `X ⊗ -` is additive on light condensed abelian groups. -/
theorem tensorLeft_additive (X : LightCondAb) : (tensorLeft X).Additive := by
  have h : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X) :=
    h.preservesColimitsOfShape
  have h3 : PreservesBinaryBiproducts (tensorLeft X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Left whiskering is additive. -/
theorem whiskerLeft_sub (X : LightCondAb) {Y Z : LightCondAb} (f g : Y ⟶ Z) :
    X ◁ (f - g) = X ◁ f - X ◁ g := by
  haveI := tensorLeft_additive X
  exact Functor.map_sub (tensorLeft X)

/-- Uncurrying is additive. -/
theorem uncurry_sub {X Y Z : LightCondAb} (f g : Y ⟶ (ihom X).obj Z) :
    MonoidalClosed.uncurry (f - g) = MonoidalClosed.uncurry f - MonoidalClosed.uncurry g := by
  rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq,
    whiskerLeft_sub, Preadditive.sub_comp]

/-- Precomposition with an isomorphism `e : B ≅ A`, as an equivalence `(A ⟶ Z) ≃ (B ⟶ Z)`. -/
def precompIsoEquiv {A B : LightCondAb} (e : B ≅ A) (Z : LightCondAb) : (A ⟶ Z) ≃ (B ⟶ Z) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := by
    show e.inv ≫ (e.hom ≫ f) = f
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  right_inv f := by
    show e.hom ≫ (e.inv ≫ f) = f
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Morphisms out of a cokernel are the morphisms out of the target which kill the map. -/
def cokerHomEquiv {X Y : LightCondAb} (g : X ⟶ Y) (A : LightCondAb) :
    (cokernel g ⟶ A) ≃ {f : Y ⟶ A // g ≫ f = 0} where
  toFun φ := ⟨cokernel.π g ≫ φ, by rw [← Category.assoc, cokernel.condition, zero_comp]⟩
  invFun f := cokernel.desc g f.1 f.2
  left_inv φ := (cancel_epi (cokernel.π g)).1 (by rw [cokernel.π_desc])
  right_inv f := Subtype.ext (cokernel.π_desc g f.1 f.2)

/-- The "generic element" of the free module `ℤ[S]` over `S`. -/
def unitElem (S : LightProfinite.{0}) : ↥((zfree S).obj.obj (op S)) :=
  ((freeForgetAdjunction ℤ).unit.app S.toCondensed).1.app (op S) (𝟙 S)

/-- Evaluation formula for `homFreeEquiv`. -/
theorem homFreeEquiv_eq_eval (S : LightProfinite.{0}) (A : LightCondAb) (g : zfree S ⟶ A) :
    homFreeEquiv S A g = g.1.app (op S) (unitElem S) := by
  simp only [homFreeEquiv, Adjunction.homEquiv_apply, yonedaEquiv_comp]
  rfl

/-- `homFreeEquiv` is additive. -/
theorem homFreeEquiv_sub (S : LightProfinite.{0}) (A : LightCondAb) (g g' : zfree S ⟶ A) :
    homFreeEquiv S A (g - g') = homFreeEquiv S A g - homFreeEquiv S A g' := by
  rw [homFreeEquiv_eq_eval, homFreeEquiv_eq_eval, homFreeEquiv_eq_eval]
  have key : (g - g').hom.app (op S) = g.hom.app (op S) - g'.hom.app (op S) := by
    have h : (-g').1.app (op S) = -(g'.1.app (op S)) :=
      eq_neg_of_add_eq_zero_left (by rw [← Sheaf.Hom.add_app, neg_add_cancel]; rfl)
    rw [sub_eq_add_neg, sub_eq_add_neg, Sheaf.Hom.add_app, h]
  rw [key]
  exact LinearMap.sub_apply _ _ _

/-- `freeTensorIso` naturality, conjugated to the inverse. -/
theorem freeTensorIso_inv_natural (S : LightProfinite.{0}) {T T' : LightProfinite.{0}}
    (f : T ⟶ T') :
    (freeTensorIso S T).inv ≫ (zfree S ◁ zfreeFunctor.map f) =
      zfreeFunctor.map (S ◁ f) ≫ (freeTensorIso S T').inv := by
  have h := freeTensorIso_natural S f
  have h2 : (zfree S ◁ zfreeFunctor.map f)
      = (freeTensorIso S T).hom ≫ zfreeFunctor.map (S ◁ f) ≫ (freeTensorIso S T').inv := by
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-! ## The locally constant model of `ΔM` -/

/-- The locally constant model `ΔM^lc` of a discrete abelian group. Its sections at `U` are
*definitionally* the locally constant functions `↥U → ↥M`. -/
abbrev lcDisc (M : ModuleCat.{0} ℤ) : LightCondAb :=
  (LightCondMod.LocallyConstant.functor ℤ).obj M

/-- The restriction maps of `ΔM^lc` are `LocallyConstant.comap`. -/
theorem lcDisc_map (M : ModuleCat.{0} ℤ) {U V : LightProfinite.{0}} (f : U ⟶ V)
    (v : LocallyConstant ↥V ↥M) :
    (lcDisc M).obj.map f.op v = LocallyConstant.comap f.hom.hom v := rfl

/-! ## The section-wise identification `(ℤ[S] ⟹ ΔM)(T) ≅ C(S × T, M)` -/

/-- The section-wise identification, as an equivalence `(ℤ[S] ⟹ ΔM)(T) ≃ C(S × T, M)`. -/
def sdPhi (M : ModuleCat.{0} ℤ) (S T : LightProfinite.{0}) :
    (zfree T ⟶ (ihom (zfree S)).obj (lcDisc M)) ≃ LocallyConstant (↥S × ↥T) ↥M :=
  (((ihom.adjunction (C := LightCondAb) (zfree S)).homEquiv (zfree T) (lcDisc M)).symm).trans
    ((precompIsoEquiv (freeTensorIso S T).symm (lcDisc M)).trans
      ((homFreeEquiv (S ⊗ T) (lcDisc M)).trans (Equiv.refl _)))

theorem sdPhi_apply (M : ModuleCat.{0} ℤ) (S T : LightProfinite.{0})
    (g : zfree T ⟶ (ihom (zfree S)).obj (lcDisc M)) :
    sdPhi M S T g = homFreeEquiv (S ⊗ T) (lcDisc M)
      ((freeTensorIso S T).inv ≫ MonoidalClosed.uncurry g) := rfl

/-- `sdPhi` is additive. -/
theorem sdPhi_sub (M : ModuleCat.{0} ℤ) (S T : LightProfinite.{0})
    (g g' : zfree T ⟶ (ihom (zfree S)).obj (lcDisc M)) :
    sdPhi M S T (g - g') = sdPhi M S T g - sdPhi M S T g' := by
  simp only [sdPhi_apply, uncurry_sub, Preadditive.comp_sub, homFreeEquiv_sub]

theorem sdPhi_zero (M : ModuleCat.{0} ℤ) (S T : LightProfinite.{0}) :
    sdPhi M S T 0 = 0 := by
  have h := sdPhi_sub M S T (0 : zfree T ⟶ (ihom (zfree S)).obj (lcDisc M)) 0
  simpa using h

/-- The shift on the sections corresponds to precomposition with `id × shift`. -/
theorem sdPhi_shift (M : ModuleCat.{0} ℤ) (S : LightProfinite.{0})
    (g : zfree (ℕ∪{∞}) ⟶ (ihom (zfree S)).obj (lcDisc M)) :
    sdPhi M S (ℕ∪{∞}) (zfreeFunctor.map LightProfinite.shift ≫ g) =
      LocallyConstant.comap (shiftProd S) (sdPhi M S (ℕ∪{∞}) g) := by
  rw [sdPhi_apply, sdPhi_apply, MonoidalClosed.uncurry_natural_left]
  have h1 : (freeTensorIso S (ℕ∪{∞})).inv ≫
        (zfree S ◁ zfreeFunctor.map LightProfinite.shift) ≫
        MonoidalClosed.uncurry g =
      zfreeFunctor.map (S ◁ LightProfinite.shift) ≫
        ((freeTensorIso S (ℕ∪{∞})).inv ≫ MonoidalClosed.uncurry g) := by
    rw [← Category.assoc, freeTensorIso_inv_natural S LightProfinite.shift, Category.assoc]
  rw [h1, homFreeEquiv_naturality, lcDisc_map]
  congr 1

/-- The vanishing condition is the vanishing of the corresponding locally constant function on
the slice at infinity. -/
theorem sdPhi_map_zero_iff (M : ModuleCat.{0} ℤ) (S : LightProfinite.{0})
    (v : LocallyConstant (↥S × ↥(ℕ∪{∞})) ↥M) :
    (lcDisc M).obj.map (whiskerLeft S ι).op v = 0 ↔ ∀ s : ↥S, v (s, ∞) = 0 := by
  rw [lcDisc_map]
  constructor
  · intro h s
    have h1 : LocallyConstant.comap ((whiskerLeft S ι).hom.hom) v
        (s, PUnit.unit) = 0 := by rw [h]; rfl
    have hp : ((whiskerLeft S ι).hom.hom) (s, PUnit.unit) = (s, ∞) := rfl
    rw [LocallyConstant.coe_comap_apply, hp] at h1
    exact h1
  · intro h
    apply LocallyConstant.ext
    intro p
    rw [LocallyConstant.coe_comap_apply]
    have hp : ((whiskerLeft S ι).hom.hom) p = (p.1, ∞) := rfl
    rw [hp]
    exact h p.1

/-- The vanishing condition transported to `Hom`-sets. -/
theorem sdPhi_vanishing (M : ModuleCat.{0} ℤ) (S : LightProfinite.{0})
    (g : zfree (ℕ∪{∞}) ⟶ (ihom (zfree S)).obj (lcDisc M)) :
    sdPhi M S (LightProfinite.of PUnit.{1}) (P_map ≫ g) =
      (lcDisc M).obj.map (whiskerLeft S ι).op (sdPhi M S (ℕ∪{∞}) g) := by
  rw [sdPhi_apply, sdPhi_apply, show P_map = zfreeFunctor.map ι from rfl,
    MonoidalClosed.uncurry_natural_left]
  have h1 : (freeTensorIso S (LightProfinite.of PUnit.{1})).inv ≫
        (zfree S ◁ zfreeFunctor.map ι) ≫ MonoidalClosed.uncurry g =
      zfreeFunctor.map (S ◁ ι) ≫
        ((freeTensorIso S (ℕ∪{∞})).inv ≫ MonoidalClosed.uncurry g) := by
    rw [← Category.assoc, freeTensorIso_inv_natural S ι, Category.assoc]
  rw [h1, homFreeEquiv_naturality]

/-! ## The cokernel relation `P_proj ≫ (1 - shift) = (1 - shift') ≫ P_proj` -/

theorem P_proj_oneMinusShift : P_proj ≫ oneMinusShift = oneMinusShift' ≫ P_proj := by
  dsimp only [oneMinusShift, P_homMk, P_proj, P]
  rw [← Category.assoc, cokernel.π_desc]

/-! ## The main result for the locally constant model -/

theorem sections_disc_lcDisc (M : ModuleCat.{0} ℤ) (S : LightProfinite.{0}) :
    ∃ e : ↥((ihomP (lcDisc M)).obj.obj (op S)) ≃ Vanishing S M,
      ∀ x : ↥((ihomP (lcDisc M)).obj.obj (op S)),
        e ((oneMinusShiftStar (lcDisc M)).hom.app (op S) x) = Vanishing.shiftDiff (e x) := by
  -- the subtype identification `{g // P_map ≫ g = 0} ≃ Vanishing S M`
  let V : {g : zfree (ℕ∪{∞}) ⟶ (ihom (zfree S)).obj (lcDisc M) // P_map ≫ g = 0} ≃
      Vanishing S M :=
    Equiv.subtypeEquiv (sdPhi M S (ℕ∪{∞})) (fun g => by
      constructor
      · intro h
        have h1 : sdPhi M S (LightProfinite.of PUnit.{1}) (P_map ≫ g) = 0 := by
          rw [h, sdPhi_zero]
        rw [sdPhi_vanishing] at h1
        exact (sdPhi_map_zero_iff M S (sdPhi M S (ℕ∪{∞}) g)).1 h1
      · intro h
        have h1 : sdPhi M S (LightProfinite.of PUnit.{1}) (P_map ≫ g) = 0 := by
          rw [sdPhi_vanishing]
          exact (sdPhi_map_zero_iff M S (sdPhi M S (ℕ∪{∞}) g)).2 h
        exact (sdPhi M S (LightProfinite.of PUnit.{1})).injective (by rw [h1, sdPhi_zero]))
  let γ : zfree S ⊗ P ≅ P ⊗ zfree S := BraidedCategory.braiding (zfree S) P
  -- the composite up to the cokernel step
  let step : ↥((ihomP (lcDisc M)).obj.obj (op S)) →
      {g : zfree (ℕ∪{∞}) ⟶ (ihom (zfree S)).obj (lcDisc M) // P_map ≫ g = 0} :=
    fun x => cokerHomEquiv P_map ((ihom (zfree S)).obj (lcDisc M))
      ((ihom.adjunction (C := LightCondAb) (zfree S)).homEquiv P (lcDisc M)
        (precompIsoEquiv γ (lcDisc M) (ihomPoints ℤ P (lcDisc M) S x)))
  refine ⟨Equiv.trans (ihomPoints ℤ P (lcDisc M) S)
      (Equiv.trans (precompIsoEquiv γ (lcDisc M))
        (Equiv.trans ((ihom.adjunction (C := LightCondAb) (zfree S)).homEquiv P (lcDisc M))
          (Equiv.trans (cokerHomEquiv P_map ((ihom (zfree S)).obj (lcDisc M))) V))),
    fun x => ?_⟩
  -- the effect of the shift on `step`
  have hstep1 : (step ((oneMinusShiftStar (lcDisc M)).hom.app (op S) x)).1 =
      oneMinusShift' ≫ (step x).1 := by
    show P_proj ≫ (ihom.adjunction (C := LightCondAb) (zfree S)).homEquiv P (lcDisc M)
        (precompIsoEquiv γ (lcDisc M) (ihomPoints ℤ P (lcDisc M) S
          ((oneMinusShiftStar (lcDisc M)).hom.app (op S) x))) = _
    rw [show oneMinusShiftStar (lcDisc M) = (MonoidalClosed.pre oneMinusShift).app (lcDisc M)
        from rfl,
      Work.REFL.ihomPoints_pre ℤ P P (lcDisc M) oneMinusShift S x, Equiv.apply_symm_apply]
    have hbraid : γ.hom ≫ (oneMinusShift ▷ ((free ℤ).obj S.toCondensed)) =
        (((free ℤ).obj S.toCondensed) ◁ oneMinusShift) ≫ γ.hom := by
      have h := BraidedCategory.braiding_naturality (C := LightCondAb)
        (𝟙 (zfree S)) oneMinusShift
      simpa [γ, MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using h.symm
    have hswap : ∀ w : P ⊗ ((free ℤ).obj S.toCondensed) ⟶ lcDisc M,
        (precompIsoEquiv γ (lcDisc M))
            ((oneMinusShift ▷ ((free ℤ).obj S.toCondensed)) ≫ w) =
          (((free ℤ).obj S.toCondensed) ◁ oneMinusShift) ≫
            (precompIsoEquiv γ (lcDisc M)) w := by
      intro w
      show γ.hom ≫ (oneMinusShift ▷ ((free ℤ).obj S.toCondensed)) ≫ w =
        (((free ℤ).obj S.toCondensed) ◁ oneMinusShift) ≫ γ.hom ≫ w
      rw [← Category.assoc, hbraid, Category.assoc]
    rw [hswap]
    rw [MonoidalClosed.homEquiv_apply_eq]
    have hc : MonoidalClosed.curry (((free ℤ).obj S.toCondensed) ◁ oneMinusShift ≫
          (precompIsoEquiv γ (lcDisc M)) ((ihomPoints ℤ P (lcDisc M) S) x))
        = oneMinusShift ≫ MonoidalClosed.curry ((precompIsoEquiv γ (lcDisc M))
            ((ihomPoints ℤ P (lcDisc M) S) x)) :=
      MonoidalClosed.curry_natural_left oneMinusShift _
    rw [hc]
    show P_proj ≫ oneMinusShift ≫ MonoidalClosed.curry ((precompIsoEquiv γ (lcDisc M))
        ((ihomPoints ℤ P (lcDisc M) S) x)) =
      oneMinusShift' ≫ (P_proj ≫ MonoidalClosed.curry ((precompIsoEquiv γ (lcDisc M))
        ((ihomPoints ℤ P (lcDisc M) S) x)))
    rw [← Category.assoc, P_proj_oneMinusShift, Category.assoc]
  have hproof : P_map ≫ (oneMinusShift' ≫ (step x).1) = 0 := by
    rw [← hstep1]
    exact (step ((oneMinusShiftStar (lcDisc M)).hom.app (op S) x)).2
  have hstep : step ((oneMinusShiftStar (lcDisc M)).hom.app (op S) x) =
      ⟨oneMinusShift' ≫ (step x).1, hproof⟩ := Subtype.ext hstep1
  -- the effect of the shift on the locally constant model
  have hϕ : sdPhi M S (ℕ∪{∞}) ((step ((oneMinusShiftStar (lcDisc M)).hom.app (op S) x)).1) =
      sdPhi M S (ℕ∪{∞}) (step x).1 -
        LocallyConstant.comap (shiftProd S) (sdPhi M S (ℕ∪{∞}) (step x).1) := by
    rw [hstep1]
    have h1 : oneMinusShift' ≫ (step x).1 =
        (step x).1 - zfreeFunctor.map LightProfinite.shift ≫ (step x).1 := by
      show (𝟙 _ - zfreeFunctor.map LightProfinite.shift) ≫ (step x).1 = _
      simp [Preadditive.sub_comp]
    rw [h1, sdPhi_sub, sdPhi_shift]
  refine Subtype.ext ?_
  show (sdPhi M S (ℕ∪{∞}) ((step ((oneMinusShiftStar (lcDisc M)).hom.app (op S) x)).1)) =
    (sdPhi M S (ℕ∪{∞}) (step x).1) -
      LocallyConstant.comap (shiftProd S) (sdPhi M S (ℕ∪{∞}) (step x).1)
  rw [hϕ]

/-! ## Transport to `ΔM` -/

theorem sections_disc (M : ModuleCat.{0} ℤ) (S : LightProfinite.{0}) :
    ∃ e : ↥((Work.DISC.ihomP (Work.DISC.disc M)).obj.obj (Opposite.op S)) ≃
        Work.DISC.Vanishing S M,
      ∀ x : ↥((Work.DISC.ihomP (Work.DISC.disc M)).obj.obj (Opposite.op S)),
        e ((Work.DISC.oneMinusShiftStar (Work.DISC.disc M)).hom.app (Opposite.op S) x) =
          Work.DISC.Vanishing.shiftDiff (e x) := by
  obtain ⟨e₀, he₀⟩ := sections_disc_lcDisc M S
  let φ : lcDisc M ≅ disc M := (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app M
  let Φmap : ↥((ihomP (lcDisc M)).obj.obj (op S)) → ↥((ihomP (disc M)).obj.obj (op S)) :=
    (((ihom P).mapIso φ).hom).1.app (op S)
  haveI : IsIso (((ihom P).mapIso φ).hom) := inferInstance
  have hbij : Function.Bijective Φmap := ConcreteCategory.isIso_iff_bijective _ |>.mp inferInstance
  let Φ : ↥((ihomP (lcDisc M)).obj.obj (op S)) ≃ ↥((ihomP (disc M)).obj.obj (op S)) :=
    Equiv.ofBijective Φmap hbij
  have hsq : ∀ x, Φ ((oneMinusShiftStar (lcDisc M)).hom.app (op S) x) =
      (oneMinusShiftStar (disc M)).hom.app (op S) (Φ x) := by
    intro x
    have h := MonoidalClosed.pre_comm_ihom_map (C := LightCondAb) oneMinusShift φ.hom
    have h2 := congrArg (fun (t : ihomP (lcDisc M) ⟶ ihomP (disc M)) =>
      (ConcreteCategory.hom (t.1.app (op S))) x) h
    show (ConcreteCategory.hom ((((ihom P).map φ.hom)).1.app (op S)))
        ((ConcreteCategory.hom (((oneMinusShiftStar (lcDisc M))).hom.app (op S))) x) =
      (ConcreteCategory.hom (((oneMinusShiftStar (disc M))).hom.app (op S)))
        ((ConcreteCategory.hom ((((ihom P).map φ.hom)).1.app (op S))) x)
    simpa only [oneMinusShiftStar, ihomP, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply] using h2
  have hs : ∀ y, Φ.symm ((oneMinusShiftStar (disc M)).hom.app (op S) y) =
      (oneMinusShiftStar (lcDisc M)).hom.app (op S) (Φ.symm y) := by
    intro y
    apply Φ.injective
    rw [Equiv.apply_symm_apply, hsq (Φ.symm y), Equiv.apply_symm_apply]
  refine ⟨Equiv.trans Φ.symm e₀, fun y => ?_⟩
  show e₀ (Φ.symm ((oneMinusShiftStar (disc M)).hom.app (op S) y)) =
    Vanishing.shiftDiff (e₀ (Φ.symm y))
  rw [hs y, he₀]

end Work.DISC
