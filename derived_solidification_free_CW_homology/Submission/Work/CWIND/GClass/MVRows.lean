import Submission.Work.CWIND.GClass.mono_AFunctor_map_incl

/-!
# The Mayer–Vietoris rows for `C`, `A` and `ℤ[-]`

This file assembles the short exact sequences used in the Mayer–Vietoris step of the CW
induction (`Work.CWIND.GClass.G_mv`):

* `SCrow` : `0 → C(U ∩ V) → C(U) ⊞ C(V) → PC → 0`, the pushout of the singular chains;
* `SArow` : `0 → A(U ∩ V) → A(U) ⊞ A(V) → PA → 0`, the pushout of the complexes `A`;
* `SZrow` : `0 → ℤ[U ∩ V] → ℤ[U] ⊞ ℤ[V] → ℤ[X] → 0` (`CondMVProp`).

Pushouts of monomorphisms give short exact sequences (`IsPushout.exact_shortComplex` and
`IsPushout.epi_shortComplex_g`); the monomorphisms are `mono_Cfun_map_incl`,
`mono_AFunctor_map_incl` and `CondMVProp`'s, and `singleFunctor 0` is mono-preserving.

The natural transformations `b : C ⟶ A` and `a : ℤ[-] ⟶ A` induce morphisms of short complexes,
and the canonical comparison maps `gammaC : PC ⟶ C(X)`, `gammaA : PA ⟶ A(X)` are related by
`gammaC ≫ b(X) = (bRow).τ₃ ≫ gammaA` and `aUV ≫ gammaA = a(X)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.GClass

variable {X : TopCat.{0}}

/-! ## Elementary lemmas -/

/-- If `f` is a monomorphism then so is `biprod.lift f (-g)`. -/
lemma mono_biprod_lift_neg {C : Type*} [Category* C] [Preadditive C] {A B D : C}
    [HasBinaryBiproduct B D] {f : A ⟶ B} {g : A ⟶ D} (hf : Mono f) :
    Mono (biprod.lift f (-g)) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro W u hu
  have h1 : u ≫ f = 0 := by
    rw [← biprod.lift_fst f (-g), ← Category.assoc, hu, zero_comp]
  exact (Preadditive.mono_iff_cancel_zero f).1 hf W u h1

/-- The zero condition for `biprod.lift f (-g)` followed by `biprod.desc a b`. -/
lemma lift_desc_eq_zero {C : Type*} [Category* C] [Preadditive C] {A B D P : C}
    [HasBinaryBiproduct B D] {f : A ⟶ B} {g : A ⟶ D} {a : B ⟶ P} {b : D ⟶ P}
    (w : f ≫ a = g ≫ b) : biprod.lift f (-g) ≫ biprod.desc a b = 0 := by
  rw [biprod.lift_desc, Preadditive.neg_comp, w, add_neg_cancel]

/-- The short complex `0 → A₁ → A₁ ⊞ A₂ → A₂ → 0`. -/
abbrev splitSes (A₁ A₂ : CochainComplex LightCondAb ℤ) :
    ShortComplex (CochainComplex LightCondAb ℤ) :=
  ShortComplex.mk (biprod.inl : A₁ ⟶ A₁ ⊞ A₂) (biprod.snd : A₁ ⊞ A₂ ⟶ A₂) (by simp)

/-- The split short complex is short exact. -/
theorem splitSes_shortExact (A₁ A₂ : CochainComplex LightCondAb ℤ) :
    (splitSes A₁ A₂).ShortExact :=
  ShortComplex.Splitting.shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct A₁ A₂)

/-- A morphism `A₁ ⊞ A₂ ⟶ B₁ ⊞ B₂` given by a pair of morphisms is a solid-equivalence if its
components are. -/
theorem biprod_solidEquiv (hTK : ToolkitProp) {A₁ A₂ B₁ B₂ : CochainComplex LightCondAb ℤ}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (hf : SolidEquiv ((DerivedCategory.Q).map f))
    (hg : SolidEquiv ((DerivedCategory.Q).map g)) :
    SolidEquiv ((DerivedCategory.Q).map (biprod.map f g)) := by
  let φ : splitSes A₁ A₂ ⟶ splitSes B₁ B₂ :=
    { τ₁ := f
      τ₂ := biprod.map f g
      τ₃ := g
      comm₁₂ := (biprod.inl_map f g).symm
      comm₂₃ := biprod.map_snd f g }
  exact hTK.ses₂ (splitSes_shortExact A₁ A₂) (splitSes_shortExact B₁ B₂) φ hf hg

/-- The inclusion `U ∩ V ⊆ U`, as a morphism of spaces. -/
abbrev mvIncl₁ (U V : Set X) : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
  Submission.Blueprint.incl (Set.inter_subset_left : U ∩ V ⊆ U)

/-- The inclusion `U ∩ V ⊆ V`, as a morphism of spaces. -/
abbrev mvIncl₂ (U V : Set X) : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
  Submission.Blueprint.incl (Set.inter_subset_right : U ∩ V ⊆ V)

@[simp]
lemma mvIncl₁_comp_inclTop (U V : Set X) :
    mvIncl₁ U V ≫ Submission.Blueprint.inclTop U =
      Submission.Blueprint.inclTop (U ∩ V : Set X) :=
  TopCat.ext (fun _ => rfl)

@[simp]
lemma mvIncl₂_comp_inclTop (U V : Set X) :
    mvIncl₂ U V ≫ Submission.Blueprint.inclTop V =
      Submission.Blueprint.inclTop (U ∩ V : Set X) :=
  TopCat.ext (fun _ => rfl)

/-- The pushout of the singular chains of `U ∩ V → U` and `U ∩ V → V`. -/
abbrev PC (U V : Set X) : CochainComplex LightCondAb ℤ :=
  pushout (Cfun.map (mvIncl₁ U V)) (Cfun.map (mvIncl₂ U V))

/-- The pushout of the complexes `A(U ∩ V) → A(U)` and `A(U ∩ V) → A(V)`. -/
abbrev PA (U V : Set X) : CochainComplex LightCondAb ℤ :=
  pushout (AFunctor.map (mvIncl₁ U V)) (AFunctor.map (mvIncl₂ U V))

/-! ## The three rows -/

/-- The Mayer–Vietoris row of the singular chains. -/
abbrev SCrow (U V : Set X) : ShortComplex (CochainComplex LightCondAb ℤ) :=
  ShortComplex.mk (biprod.lift (Cfun.map (mvIncl₁ U V)) (-(Cfun.map (mvIncl₂ U V))))
    (biprod.desc (pushout.inl (Cfun.map (mvIncl₁ U V)) (Cfun.map (mvIncl₂ U V)))
      (pushout.inr (Cfun.map (mvIncl₁ U V)) (Cfun.map (mvIncl₂ U V))))
    (lift_desc_eq_zero pushout.condition)

/-- The Mayer–Vietoris row of the complexes `A`. -/
abbrev SArow (U V : Set X) : ShortComplex (CochainComplex LightCondAb ℤ) :=
  ShortComplex.mk (biprod.lift (AFunctor.map (mvIncl₁ U V)) (-(AFunctor.map (mvIncl₂ U V))))
    (biprod.desc (pushout.inl (AFunctor.map (mvIncl₁ U V)) (AFunctor.map (mvIncl₂ U V)))
      (pushout.inr (AFunctor.map (mvIncl₁ U V)) (AFunctor.map (mvIncl₂ U V))))
    (lift_desc_eq_zero pushout.condition)

/-- The Mayer–Vietoris row of `ℤ[-]`, as the image of `CondMVProp`'s pushout under
`singleFunctor 0`. -/
theorem ZrowPushout (hCondMV : CondMVProp) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) :
    IsPushout (Zfun.map (mvIncl₁ U V)) (Zfun.map (mvIncl₂ U V))
      (Zfun.map (Submission.Blueprint.inclTop U))
      (Zfun.map (Submission.Blueprint.inclTop V)) :=
  Functor.map_isPushout (CochainComplex.singleFunctor LightCondAb 0)
    (hCondMV X U V hU hV hUV).2

/-- The Mayer–Vietoris row of `ℤ[-]`. -/
abbrev SZrow (hCondMV : CondMVProp) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) : ShortComplex (CochainComplex LightCondAb ℤ) :=
  ShortComplex.mk (biprod.lift (Zfun.map (mvIncl₁ U V)) (-(Zfun.map (mvIncl₂ U V))))
    (biprod.desc (Zfun.map (Submission.Blueprint.inclTop U))
      (Zfun.map (Submission.Blueprint.inclTop V)))
    (lift_desc_eq_zero (ZrowPushout hCondMV U V hU hV hUV).w)

/-- The comparison between the canonical forms of the rows. -/
lemma SCrow_eq (U V : Set X) :
    SCrow U V =
      (IsPushout.of_hasPushout (Cfun.map (mvIncl₁ U V)) (Cfun.map (mvIncl₂ U V))).shortComplex :=
  rfl

/-- The comparison between the canonical forms of the rows. -/
lemma SArow_eq (U V : Set X) :
    SArow U V =
      (IsPushout.of_hasPushout (AFunctor.map (mvIncl₁ U V))
        (AFunctor.map (mvIncl₂ U V))).shortComplex :=
  rfl

/-- The comparison between the canonical forms of the rows. -/
lemma SZrow_eq (hCondMV : CondMVProp) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) :
    SZrow hCondMV U V hU hV hUV = (ZrowPushout hCondMV U V hU hV hUV).shortComplex :=
  rfl

/-- The singular chain row is short exact. -/
theorem SCrow_shortExact (U V : Set X) : (SCrow U V).ShortExact := by
  rw [SCrow_eq U V]
  have hp := IsPushout.of_hasPushout (Cfun.map (mvIncl₁ U V)) (Cfun.map (mvIncl₂ U V))
  refine ShortComplex.ShortExact.mk' hp.exact_shortComplex ?_ hp.epi_shortComplex_g
  exact mono_biprod_lift_neg (mono_Cfun_map_incl (Set.inter_subset_left : U ∩ V ⊆ U))

/-- The `A`-row is short exact. -/
theorem SArow_shortExact (U V : Set X) : (SArow U V).ShortExact := by
  rw [SArow_eq U V]
  have hp := IsPushout.of_hasPushout (AFunctor.map (mvIncl₁ U V)) (AFunctor.map (mvIncl₂ U V))
  refine ShortComplex.ShortExact.mk' hp.exact_shortComplex ?_ hp.epi_shortComplex_g
  exact mono_biprod_lift_neg (mono_AFunctor_map_incl (Set.inter_subset_left : U ∩ V ⊆ U))

/-- The `ℤ[-]`-row is short exact. -/
theorem SZrow_shortExact (hCondMV : CondMVProp) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) : (SZrow hCondMV U V hU hV hUV).ShortExact := by
  rw [SZrow_eq hCondMV U V hU hV hUV]
  have hp := ZrowPushout hCondMV U V hU hV hUV
  refine ShortComplex.ShortExact.mk' hp.exact_shortComplex ?_ hp.epi_shortComplex_g
  have h₁ : Mono (freeLightCondAbOfTopFunctor.map (mvIncl₁ U V)) :=
    (hCondMV X U V hU hV hUV).1
  haveI := (inferInstance : Functor.PreservesMonomorphisms
    (CochainComplex.singleFunctor LightCondAb 0))
  have h₂ : Mono (Zfun.map (mvIncl₁ U V)) := by
    haveI : Mono (freeLightCondAbOfTopFunctor.map (mvIncl₁ U V)) := h₁
    exact (inferInstance : Functor.PreservesMonomorphisms
      (CochainComplex.singleFunctor LightCondAb 0)).preserves
      (freeLightCondAbOfTopFunctor.map (mvIncl₁ U V))
  exact mono_biprod_lift_neg h₂

/-! ## The comparison maps -/

/-- The third component of the morphism of short complexes induced by `b : C ⟶ A`. -/
noncomputable def bRowTau₃ (U V : Set X)
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) : PC U V ⟶ PA U V :=
  pushout.desc (b.app (TopCat.of U) ≫ pushout.inl (AFunctor.map (mvIncl₁ U V))
      (AFunctor.map (mvIncl₂ U V)))
    (b.app (TopCat.of V) ≫ pushout.inr (AFunctor.map (mvIncl₁ U V))
      (AFunctor.map (mvIncl₂ U V)))
    (by
      rw [← Category.assoc, b.naturality, Category.assoc, pushout.condition, ← Category.assoc,
        ← b.naturality, Category.assoc])

lemma bRowTau₃_inl (U V : Set X)
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) :
    pushout.inl (Cfun.map (mvIncl₁ U V)) (Cfun.map (mvIncl₂ U V)) ≫ bRowTau₃ U V b =
      b.app (TopCat.of U) ≫ pushout.inl (AFunctor.map (mvIncl₁ U V))
        (AFunctor.map (mvIncl₂ U V)) := by
  rw [bRowTau₃, Limits.pushout.inl_desc]

lemma bRowTau₃_inr (U V : Set X)
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) :
    pushout.inr (Cfun.map (mvIncl₁ U V)) (Cfun.map (mvIncl₂ U V)) ≫ bRowTau₃ U V b =
      b.app (TopCat.of V) ≫ pushout.inr (AFunctor.map (mvIncl₁ U V))
        (AFunctor.map (mvIncl₂ U V)) := by
  rw [bRowTau₃, Limits.pushout.inr_desc]

/-- The morphism of short exact sequences induced by `b : C ⟶ A`. -/
noncomputable def bRow (U V : Set X)
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) : SCrow U V ⟶ SArow U V where
  τ₁ := b.app (TopCat.of (U ∩ V : Set X))
  τ₂ := biprod.map (b.app (TopCat.of U)) (b.app (TopCat.of V))
  τ₃ := bRowTau₃ U V b
  comm₁₂ := by
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst, ← Category.assoc,
        biprod.lift_fst]
      exact (b.naturality (mvIncl₁ U V)).symm
    · rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd, ← Category.assoc,
        biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg]
      exact congrArg Neg.neg (b.naturality (mvIncl₂ U V)).symm
  comm₂₃ := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc]
      rw [← Category.assoc, biprod.inl_desc, bRowTau₃_inl]
    · rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc]
      rw [← Category.assoc, biprod.inr_desc, bRowTau₃_inr]

/-- The canonical comparison map `PC ⟶ C(X)`. -/
noncomputable def gammaC (U V : Set X) : PC U V ⟶ Cfun.obj X :=
  pushout.desc (GG.map (singC.map (Submission.Blueprint.inclTop U)))
    (GG.map (singC.map (Submission.Blueprint.inclTop V)))
    (by
      rw [show Cfun.map (mvIncl₁ U V) = GG.map (singC.map (mvIncl₁ U V)) from rfl,
        show Cfun.map (mvIncl₂ U V) = GG.map (singC.map (mvIncl₂ U V)) from rfl,
        ← GG.map_comp, ← GG.map_comp, ← Functor.map_comp, ← Functor.map_comp,
        mvIncl₁_comp_inclTop, mvIncl₂_comp_inclTop])

/-- The canonical comparison map `PA ⟶ A(X)`. -/
noncomputable def gammaA (U V : Set X) : PA U V ⟶ AFunctor.obj X :=
  pushout.desc (AFunctor.map (Submission.Blueprint.inclTop U))
    (AFunctor.map (Submission.Blueprint.inclTop V))
    (by rw [← Functor.map_comp, ← Functor.map_comp, mvIncl₁_comp_inclTop,
      mvIncl₂_comp_inclTop])

/-- The canonical comparison map `ℤ[X] ⟶ PA`. -/
noncomputable def aUV (hCondMV : CondMVProp) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ)
    (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor) :
    Zfun.obj X ⟶ PA U V :=
  (ZrowPushout hCondMV U V hU hV hUV).desc
    (a.app (TopCat.of U) ≫ pushout.inl (AFunctor.map (mvIncl₁ U V))
      (AFunctor.map (mvIncl₂ U V)))
    (a.app (TopCat.of V) ≫ pushout.inr (AFunctor.map (mvIncl₁ U V))
      (AFunctor.map (mvIncl₂ U V)))
    (by
      rw [← Category.assoc, a.naturality, Category.assoc, pushout.condition, ← Category.assoc,
        ← a.naturality, Category.assoc])

/-- The morphism of short exact sequences induced by `a : ℤ[-] ⟶ A`. -/
noncomputable def aRow (hCondMV : CondMVProp) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ)
    (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor) :
    SZrow hCondMV U V hU hV hUV ⟶ SArow U V where
  τ₁ := a.app (TopCat.of (U ∩ V : Set X))
  τ₂ := biprod.map (a.app (TopCat.of U)) (a.app (TopCat.of V))
  τ₃ := aUV hCondMV U V hU hV hUV a
  comm₁₂ := by
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst, ← Category.assoc,
        biprod.lift_fst]
      exact (a.naturality (mvIncl₁ U V)).symm
    · rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd, ← Category.assoc,
        biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg]
      exact congrArg Neg.neg (a.naturality (mvIncl₂ U V)).symm
  comm₂₃ := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc]
      rw [← Category.assoc, biprod.inl_desc, aUV, IsPushout.inl_desc]
    · rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc]
      rw [← Category.assoc, biprod.inr_desc, aUV, IsPushout.inr_desc]

/-- The two comparison maps are related through `b`. -/
theorem gammaC_comp_b (U V : Set X)
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) :
    gammaC U V ≫ b.app X = (bRow U V b).τ₃ ≫ gammaA U V := by
  have hτ : (bRow U V b).τ₃ = bRowTau₃ U V b := rfl
  rw [hτ]
  have hnatU : GG.map (singC.map (Submission.Blueprint.inclTop U)) ≫ b.app X =
      b.app (TopCat.of U) ≫ AFunctor.map (Submission.Blueprint.inclTop U) :=
    b.naturality (Submission.Blueprint.inclTop U)
  have hnatV : GG.map (singC.map (Submission.Blueprint.inclTop V)) ≫ b.app X =
      b.app (TopCat.of V) ≫ AFunctor.map (Submission.Blueprint.inclTop V) :=
    b.naturality (Submission.Blueprint.inclTop V)
  apply Limits.pushout.hom_ext
  · rw [← Category.assoc, gammaC, Limits.pushout.inl_desc, hnatU, ← Category.assoc,
      bRowTau₃_inl, Category.assoc, gammaA, Limits.pushout.inl_desc]
  · rw [← Category.assoc, gammaC, Limits.pushout.inr_desc, hnatV, ← Category.assoc,
      bRowTau₃_inr, Category.assoc, gammaA, Limits.pushout.inr_desc]

/-- `a^{UV}` followed by `gammaA` is `a(X)`. -/
theorem aUV_comp_gammaA (hCondMV : CondMVProp) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ)
    (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor) :
    aUV hCondMV U V hU hV hUV a ≫ gammaA U V = a.app X := by
  have hnatU : Zfun.map (Submission.Blueprint.inclTop U) ≫ a.app X =
      a.app (TopCat.of U) ≫ AFunctor.map (Submission.Blueprint.inclTop U) :=
    a.naturality (Submission.Blueprint.inclTop U)
  have hnatV : Zfun.map (Submission.Blueprint.inclTop V) ≫ a.app X =
      a.app (TopCat.of V) ≫ AFunctor.map (Submission.Blueprint.inclTop V) :=
    a.naturality (Submission.Blueprint.inclTop V)
  apply IsPushout.hom_ext (ZrowPushout hCondMV U V hU hV hUV)
  · rw [← Category.assoc, aUV, IsPushout.inl_desc, hnatU, Category.assoc, gammaA,
      Limits.pushout.inl_desc]
  · rw [← Category.assoc, aUV, IsPushout.inr_desc, hnatV, Category.assoc, gammaA,
      Limits.pushout.inr_desc]

/-- The quasi-isomorphism provided by `SingMVProp`. -/
theorem gammaC_quasiIso (hSingMV : SingMVProp) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) : QuasiIso (gammaC U V) := by
  have h2 : gammaC U V = pushout.desc
      (GG.map (singC.map (Submission.Blueprint.inclTop U)))
      (GG.map (singC.map (Submission.Blueprint.inclTop V)))
      (by
        rw [show Cfun.map (mvIncl₁ U V) = GG.map (singC.map (mvIncl₁ U V)) from rfl,
          show Cfun.map (mvIncl₂ U V) = GG.map (singC.map (mvIncl₂ U V)) from rfl,
          ← GG.map_comp, ← GG.map_comp, ← Functor.map_comp, ← Functor.map_comp,
          mvIncl₁_comp_inclTop, mvIncl₂_comp_inclTop]) := rfl
  rw [h2]
  exact GG_quasiIso_pushout_desc
    (f₁ := singC.map (mvIncl₁ U V)) (f₂ := singC.map (mvIncl₂ U V))
    (a₁ := singC.map (Submission.Blueprint.inclTop U))
    (a₂ := singC.map (Submission.Blueprint.inclTop V))
    (by rw [← Functor.map_comp, ← Functor.map_comp, mvIncl₁_comp_inclTop, mvIncl₂_comp_inclTop])
    (hSingMV X U V hU hV hUV)

/-- **CWIND/T8**: `GOf b` is closed under Mayer–Vietoris for open covers. -/
theorem GOf_mv (hTK : ToolkitProp) (hCondMV : CondMVProp) (hSingMV : SingMVProp)
    (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor)
    (hA : ∀ (Y : TopCat.{0}) [T2Space Y], SolidEquiv ((DerivedCategory.Q).map (a.app Y)))
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor)
    (X : TopCat.{0}) [T2Space X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ)
    (hGU : GOf b (TopCat.of U)) (hGV : GOf b (TopCat.of V))
    (hGUV : GOf b (TopCat.of (U ∩ V : Set X))) :
    GOf b X := by
  haveI hU2 : T2Space (TopCat.of U) := hGU.1
  haveI hV2 : T2Space (TopCat.of V) := hGV.1
  haveI hUV2 : T2Space (TopCat.of (U ∩ V : Set X)) := hGUV.1
  refine ⟨inferInstance, ?_⟩
  have hτ₁ : SolidEquiv ((DerivedCategory.Q).map (bRow U V b).τ₁) := hGUV.2
  have hτ₂ : SolidEquiv ((DerivedCategory.Q).map (bRow U V b).τ₂) :=
    biprod_solidEquiv hTK _ _ hGU.2 hGV.2
  have hτ₃ : SolidEquiv ((DerivedCategory.Q).map (bRow U V b).τ₃) :=
    hTK.ses₃ (SCrow_shortExact U V) (SArow_shortExact U V) (bRow U V b) hτ₁ hτ₂
  have hσ₁ : SolidEquiv ((DerivedCategory.Q).map (aRow hCondMV U V hU hV hUV a).τ₁) :=
    hA _
  have hσ₂ : SolidEquiv ((DerivedCategory.Q).map (aRow hCondMV U V hU hV hUV a).τ₂) :=
    biprod_solidEquiv hTK _ _ (hA _) (hA _)
  have hσ₃ : SolidEquiv ((DerivedCategory.Q).map (aUV hCondMV U V hU hV hUV a)) :=
    hTK.ses₃ (SZrow_shortExact hCondMV U V hU hV hUV) (SArow_shortExact U V)
      (aRow hCondMV U V hU hV hUV a) hσ₁ hσ₂
  have hγA : SolidEquiv ((DerivedCategory.Q).map (gammaA U V)) := by
    have hcomp : SolidEquiv ((DerivedCategory.Q).map (aUV hCondMV U V hU hV hUV a) ≫
        (DerivedCategory.Q).map (gammaA U V)) := by
      rw [← DerivedCategory.Q.map_comp, aUV_comp_gammaA]
      exact hA X
    exact hTK.of_comp_left _ _ hσ₃ hcomp
  have hglue : (DerivedCategory.Q).map (gammaC U V) ≫ (DerivedCategory.Q).map (b.app X) =
      (DerivedCategory.Q).map (bRow U V b).τ₃ ≫ (DerivedCategory.Q).map (gammaA U V) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, gammaC_comp_b]
  have hgb : SolidEquiv ((DerivedCategory.Q).map (gammaC U V) ≫
      (DerivedCategory.Q).map (b.app X)) := by
    rw [hglue]
    exact hTK.comp _ _ hτ₃ hγA
  haveI : IsIso ((DerivedCategory.Q).map (gammaC U V)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb _).2
      (gammaC_quasiIso hSingMV U V hU hV hUV)
  have hγC : SolidEquiv ((DerivedCategory.Q).map (gammaC U V)) := hTK.of_iso _ inferInstance
  exact hTK.of_comp_left _ _ hγC hgb

end Work.CWIND.GClass
