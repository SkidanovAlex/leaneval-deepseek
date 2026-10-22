/-
AREA DERFORMAL — B1(b) and B2.

`B1(b)`: if `K` is solid-cofibrant then the solidification adjunction identifies
`Hom_D(Q(solC K), Q N)` with `Hom_D(Q K, Q(incC N))` (`homDEquiv`, natural in `K`); this is B1
of REFS/02 §1.

`B2`: quasi-isomorphisms between solid-cofibrant complexes are sent to quasi-isomorphisms by
degreewise solidification.

The K-projectivity of `solC K` (part (a) of B1) is taken here as an explicit hypothesis
`hproj`, so that this file does not depend on the order in which the pieces are proved; it is
discharged in `Package.lean` by `Work.DERFORMAL.B1KProjective`.
-/
import Submission.Work.DERFORMAL.Setup
import Submission.Work.DERFORMAL.Gen.PrecompBijective

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.DERFORMAL

variable [isSolid.ι.IsRightAdjoint]

/-! ## Helpers on hom-types -/

/-- Pre-composition with an isomorphism is a bijection. -/
lemma bijective_precomp_of_isIso {C : Type*} [Category C] {X Y : C} (u : X ⟶ Y) [IsIso u]
    (Z : C) : Function.Bijective (fun f : Y ⟶ Z => u ≫ f) :=
  ⟨fun f g h => by simpa using congrArg (fun t => inv u ≫ t) h,
    fun g => ⟨inv u ≫ g, by simp⟩⟩

/-- Pre-composition with an isomorphism is a bijection. -/
lemma bijective_precomp_iso {C : Type*} [Category C] {X X' Z : C} (e : X ≅ X') :
    Function.Bijective (fun f : X' ⟶ Z => e.hom ≫ f) :=
  bijective_precomp_of_isIso e.hom Z

/-- Post-composition with an isomorphism is a bijection. -/
lemma bijective_postcomp_iso {C : Type*} [Category C] {Y Z Z' : C} (e : Z ≅ Z') :
    Function.Bijective (fun f : Y ⟶ Z => f ≫ e.hom) :=
  ⟨fun f g h => by simpa using congrArg (fun t => t ≫ e.inv) h,
    fun g => ⟨g ≫ e.inv, by simp⟩⟩

/-- Bijectivity of `u ≫ ·` is invariant under isomorphism of the target. -/
lemma bijective_precomp_target_iso {C : Type*} [Category C] {X Y Z Z' : C} (u : X ⟶ Y)
    (e : Z ≅ Z') :
    Function.Bijective (fun f : Y ⟶ Z => u ≫ f) ↔
      Function.Bijective (fun f : Y ⟶ Z' => u ≫ f) := by
  have hK : Function.Bijective (fun t : X ⟶ Z' => t ≫ e.inv) :=
    bijective_postcomp_iso e.symm
  have hH : Function.Bijective (fun f : Y ⟶ Z => f ≫ e.hom) := bijective_postcomp_iso e
  have hΦ : (fun f : Y ⟶ Z => u ≫ f) =
      (fun t : X ⟶ Z' => t ≫ e.inv) ∘ (fun f : Y ⟶ Z' => u ≫ f) ∘
        (fun f : Y ⟶ Z => f ≫ e.hom) := by
    funext f
    simp
  rw [hΦ]
  exact ⟨fun hh => (Function.Bijective.of_comp_iff _ hH).mp
      ((Function.Bijective.of_comp_iff' hK _).mp hh),
    fun hh => hK.comp (hh.comp hH)⟩

/-- Bijectivity of `u ≫ ·` is invariant under conjugation by isomorphisms. -/
lemma bijective_precomp_iso_conj {C : Type*} [Category C] {X X' Y Y' Z : C} (u : X ⟶ Y)
    (u' : X' ⟶ Y') (e₁ : X ≅ X') (e₂ : Y ≅ Y') (h : u = e₁.hom ≫ u' ≫ e₂.inv) :
    Function.Bijective (fun f : Y ⟶ Z => u ≫ f) ↔
      Function.Bijective (fun f : Y' ⟶ Z => u' ≫ f) := by
  have hK : Function.Bijective (fun t : X' ⟶ Z => e₁.hom ≫ t) := bijective_precomp_iso e₁
  have hH : Function.Bijective (fun f : Y ⟶ Z => e₂.inv ≫ f) :=
    bijective_precomp_of_isIso e₂.inv Z
  have hΦ : (fun f : Y ⟶ Z => u ≫ f) =
      (fun t : X' ⟶ Z => e₁.hom ≫ t) ∘ (fun f : Y' ⟶ Z => u' ≫ f) ∘
        (fun f : Y ⟶ Z => e₂.inv ≫ f) := by
    funext f
    simp only [Function.comp_apply, h, Category.assoc]
  rw [hΦ]
  exact ⟨fun hh => (Function.Bijective.of_comp_iff _ hH).mp
      ((Function.Bijective.of_comp_iff' hK _).mp hh),
    fun hh => hK.comp (hh.comp hH)⟩

/-- Transport of `IsIso` along a conjugation by isomorphisms. -/
lemma isIso_of_iso_conj {C : Type*} [Category C] {A B A' B' : C} (u : A ⟶ B) (u' : A' ⟶ B')
    (e₁ : A ≅ A') (e₂ : B ≅ B') (h : u = e₁.hom ≫ u' ≫ e₂.inv) : IsIso u ↔ IsIso u' := by
  subst h
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- Compatibility of the inverse of a bijection with a pair of compatible maps. -/
lemma equiv_ofBijective_symm_comp' {α β α' β' : Type*} (e : α ≃ β) (e' : α' ≃ β')
    (F : α' → α) (G : β' → β) (h : ∀ a, e (F a) = G (e' a)) (b : β') :
    e.symm (G b) = F (e'.symm b) := by
  rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]

/-- Companion of `equiv_ofBijective_symm_comp'` (forward form). -/
lemma ofBijective_comp' {α β α' β' : Type*} (e : α ≃ β) (e' : α' ≃ β')
    (F : α' → α) (G : β' → β) (h : ∀ a, e (F a) = G (e' a)) (a : α') :
    e (F a) = G (e' a) := h a

/-- Transport of bijectivity along a conjugation by equivalences of hom-types. -/
lemma bijective_of_equiv_conj {α β α' β' : Type*} (F : α → β) (G : α' → β')
    (e : α ≃ α') (e' : β ≃ β') (h : ∀ a, e' (F a) = G (e a)) :
    Function.Bijective F ↔ Function.Bijective G := by
  have hF : F = e'.symm ∘ G ∘ e := by
    funext a
    rw [Function.comp_apply, Function.comp_apply, ← h a, Equiv.symm_apply_apply]
  rw [hF]
  exact ⟨fun hh => (Function.Bijective.of_comp_iff _ e.bijective).mp
      ((Function.Bijective.of_comp_iff' e'.symm.bijective _).mp hh),
    fun hh => e'.symm.bijective.comp (hh.comp e.bijective)⟩

/-! ## B1(b): the hom-computation -/

/-- The bijection on homotopy classes of maps provided by K-projectivity of `solC K`. -/
theorem kprojBijective (hproj : ∀ K, Cofibrant K → CochainComplex.IsKProjective (solC.obj K))
    (K : Cpx) (hK : Cofibrant K) (N : SCpx) :
    Function.Bijective (fun f : hs (solC.obj K) ⟶ hs N => Qh.map f) := by
  have h : CochainComplex.IsKProjective (solC.obj K) := hproj K hK
  exact CochainComplex.IsKProjective.Qh_map_bijective (solC.obj K) (hs N)

/-- The bijection on homotopy classes of maps provided by solid-cofibrancy of `K`. -/
theorem cofBijective (K : Cpx) (hK : Cofibrant K) (N : SCpx) :
    Function.Bijective (fun f : hq K ⟶ hq (incC.obj N) => Qh.map f) := hK N

/-- **B1(b)** (REFS/02 §1).  For a solid-cofibrant complex `K` and a complex `N` of solid
objects, the solidification adjunction together with the K-projectivity of `solC K` and the
solid-cofibrancy of `K` identifies morphisms `Q(solC K) ⟶ Q N` in the derived category with
morphisms `Q K ⟶ Q(incC N)`. -/
noncomputable def homDEquiv (hproj : ∀ K, Cofibrant K → CochainComplex.IsKProjective (solC.obj K))
    (K : Cpx) (hK : Cofibrant K) (N : SCpx) :
    (Qh.obj (hs (solC.obj K)) ⟶ Qh.obj (hs N)) ≃
      (Qh.obj (hq K) ⟶ Qh.obj (hq (incC.obj N))) :=
  (Equiv.ofBijective _ (kprojBijective hproj K hK N)).symm.trans
    ((homKEquiv K N).trans (Equiv.ofBijective _ (cofBijective K hK N)))

/-- Naturality of `homDEquiv` in the first variable. -/
lemma homDEquiv_naturality (hproj : ∀ K, Cofibrant K → CochainComplex.IsKProjective (solC.obj K))
    {K K' : Cpx} (hK : Cofibrant K) (hK' : Cofibrant K') (f : K ⟶ K') (N : SCpx)
    (g : Qh.obj (hs (solC.obj K')) ⟶ Qh.obj (hs N)) :
    homDEquiv hproj K hK N (Qh.map (qs.map (solC.map f)) ≫ g) =
      Qh.map (qc.map f) ≫ homDEquiv hproj K' hK' N g := by
  have h₁ := equiv_ofBijective_symm_comp'
    (Equiv.ofBijective _ (kprojBijective hproj K hK N))
    (Equiv.ofBijective _ (kprojBijective hproj K' hK' N))
    (fun a => qs.map (solC.map f) ≫ a) (fun b => Qh.map (qs.map (solC.map f)) ≫ b)
    (fun a => by
      change Qh.map (qs.map (solC.map f) ≫ a) = Qh.map (qs.map (solC.map f)) ≫ Qh.map a
      rw [Functor.map_comp]) g
  dsimp only [homDEquiv]
  simp only [Equiv.trans_apply]
  rw [h₁, homKEquiv_naturality]
  exact ofBijective_comp'
    (Equiv.ofBijective _ (cofBijective K hK N))
    (Equiv.ofBijective _ (cofBijective K' hK' N))
    (fun a => qc.map f ≫ a) (fun b => Qh.map (qc.map f) ≫ b)
    (fun a => by
      change Qh.map (qc.map f ≫ a) = Qh.map (qc.map f) ≫ Qh.map a
      rw [Functor.map_comp]) _

/-! ## B2 -/

/-- **B2** (REFS/02 §1).  A quasi-isomorphism between solid-cofibrant complexes is sent to a
quasi-isomorphism by degreewise solidification. -/
theorem B2 (hproj : ∀ K, Cofibrant K → CochainComplex.IsKProjective (solC.obj K))
    {K K' : Cpx} (hK : Cofibrant K) (hK' : Cofibrant K') {f : K ⟶ K'} (hf : QuasiIso f) :
    QuasiIso (solC.map f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso (C := Solid) (solC.map f)]
  set w : Qh.obj (hs (solC.obj K)) ⟶ Qh.obj (hs (solC.obj K')) :=
    Qh.map (qs.map (solC.map f)) with hw
  set v : Qh.obj (hq K) ⟶ Qh.obj (hq K') := Qh.map (qc.map f) with hv
  have hW : Qs.map (solC.map f) =
      (DerivedCategory.quotientCompQhIso Solid).inv.app (solC.obj K) ≫ w ≫
        (DerivedCategory.quotientCompQhIso Solid).hom.app (solC.obj K') := by
    rw [hw, DerivedCategory.quotientCompQhIso_hom_naturality (C := Solid) (f := solC.map f)]
    exact (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso Solid).app (solC.obj K))
      (Qs.map (solC.map f))).symm
  have hV : Q.map f = (DerivedCategory.quotientCompQhIso LightCondAb).inv.app K ≫ v ≫
      (DerivedCategory.quotientCompQhIso LightCondAb).hom.app K' := by
    rw [hv, DerivedCategory.quotientCompQhIso_hom_naturality (C := LightCondAb) (f := f)]
    exact (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso LightCondAb).app K)
      (Q.map f)).symm
  have hv' : IsIso v :=
    (isIso_of_iso_conj (Q.map f) v ((DerivedCategory.quotientCompQhIso LightCondAb).app K).symm
      ((DerivedCategory.quotientCompQhIso LightCondAb).app K').symm hV).mp inferInstance
  rw [Gen.PrecompBijective]
  intro Z
  obtain ⟨N, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Qs Z
  rw [← bijective_precomp_target_iso (Qs.map (solC.map f)) e]
  rw [← bijective_precomp_target_iso (Qs.map (solC.map f))
    ((DerivedCategory.quotientCompQhIso Solid).app N)]
  rw [bijective_precomp_iso_conj _ w ((DerivedCategory.quotientCompQhIso Solid).symm.app (solC.obj K))
    ((DerivedCategory.quotientCompQhIso Solid).symm.app (solC.obj K')) hW]
  exact (bijective_of_equiv_conj
    (fun g : Qh.obj (hs (solC.obj K')) ⟶ Qh.obj (hs N) => w ≫ g)
    (fun g : Qh.obj (hq K') ⟶ Qh.obj (hq (incC.obj N)) => v ≫ g)
    (homDEquiv hproj K' hK' N) (homDEquiv hproj K hK N)
    (fun g => homDEquiv_naturality hproj hK hK' f N g)).mpr (bijective_precomp_of_isIso v _)

end Work.DERFORMAL
