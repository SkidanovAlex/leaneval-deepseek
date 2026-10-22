/-
# The localization `K(LightCondAb) ⟶ D(LightCondAb)` preserves small coproducts

The main result of this file is `Qh_sigma_bijective`: the localization functor
`Qh : K(LightCondAb) ⟶ D(LightCondAb)` of the homotopy category at the quasi-isomorphisms
preserves small coproducts, i.e. for every family `K : J → Cpx` with a coproduct and every
object `Z` of the derived category, the canonical map

  `Hom_D(Qh (hq (∐ K)), Z) ⟶ ∏ j, Hom_D(Qh (hq (K j)), Z),   φ ↦ (Qh (hq (ι j)) ≫ φ) j`

is a bijection.

Both calculi of fractions are used, together with the two inputs which are proved elsewhere in
the workspace:

* `Work.TOOLKIT.Coprod.hq_sigma_bijective` (`hq` preserves small coproducts);
* `Work.TOOLKIT.Coprod.quasiIso_colimMap` (quasi-isomorphisms are stable under coproducts).

The strategy is the usual one for a localization: a morphism out of `Qh A` into `Qh B` is a
fraction, and the fraction is replaced by a morphism out of a coproduct so that the universal
property of the coproduct (in the homotopy category) can be applied.
-/
import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances
import Submission.Work.TOOLKIT.Coprod.hq_sigma_bijective
import Submission.Work.TOOLKIT.Coprod.quasiIso_colimMap

open CategoryTheory Limits

set_option linter.style.haveILetI false

noncomputable section

namespace Work.TOOLKIT.Coprod

/-! ## The localization functors at hand -/

/-- The quotient functor `Cpx ⟶ K(LightCondAb)`. -/
private abbrev qF : Work.TOOLKIT.Cpx ⥤ Work.TOOLKIT.KCat :=
  HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)

/-- The class of quasi-isomorphisms in the homotopy category. -/
private abbrev wq : MorphismProperty Work.TOOLKIT.KCat :=
  HomotopyCategory.quasiIso LightCondAb (ComplexShape.up ℤ)

/-! ## Two elementary bijectivity lemmas -/

/-- Postcomposition with an isomorphism is a bijection on `Hom` sets. -/
private lemma bijective_postcomp_iso {C : Type*} [Category C] {A B Z : C} (e : A ≅ B) :
    Function.Bijective (fun u : Z ⟶ A => u ≫ e.hom) :=
  ⟨fun a b h => by simpa using (cancel_mono e.hom).mp h,
    fun v => ⟨v ≫ e.inv, by simp [Category.assoc]⟩⟩

/-- Postcomposition with an isomorphism, componentwise on a dependent product of `Hom` sets. -/
private lemma bijective_pi_post {C : Type*} [Category C] {I : Type} {S : I → C} {A B : C}
    (e : A ≅ B) :
    Function.Bijective (fun v : (i : I) → S i ⟶ A => fun i => v i ≫ e.hom) := by
  constructor
  · intro v w h
    funext i
    exact (cancel_mono e.hom).mp (congrFun h i)
  · intro w
    exact ⟨fun i => w i ≫ e.inv, by funext i; simp [Category.assoc]⟩

/-- Bijectivity of the "components" map is invariant under replacing the target by an
isomorphic object: this is how the reduction to a target in the image of `Qh` is performed. -/
private lemma bijective_conj_target {C : Type*} [Category C] {I : Type} {S : I → C} {X Z Z' : C}
    (c : ∀ i, S i ⟶ X) (e : Z ≅ Z') :
    Function.Bijective (fun f : X ⟶ Z => fun i => c i ≫ f) ↔
      Function.Bijective (fun f : X ⟶ Z' => fun i => c i ≫ f) := by
  constructor
  · intro h
    have hcomp : (fun f : X ⟶ Z' => fun i => c i ≫ f) =
        (fun v : (i : I) → S i ⟶ Z => fun i => v i ≫ e.hom) ∘
          (fun f : X ⟶ Z => fun i => c i ≫ f) ∘ (fun f : X ⟶ Z' => f ≫ e.inv) := by
      funext f i
      simp only [Function.comp_apply]
      rw [Category.assoc]
      simp
    rw [hcomp]
    exact (bijective_pi_post e).comp (h.comp (bijective_postcomp_iso e.symm))
  · intro h
    have hcomp : (fun f : X ⟶ Z => fun i => c i ≫ f) =
        (fun v : (i : I) → S i ⟶ Z' => fun i => v i ≫ e.inv) ∘
          (fun f : X ⟶ Z' => fun i => c i ≫ f) ∘ (fun f : X ⟶ Z => f ≫ e.hom) := by
      funext f i
      simp only [Function.comp_apply]
      rw [Category.assoc]
      simp
    rw [hcomp]
    exact (bijective_pi_post e.symm).comp (h.comp (bijective_postcomp_iso e))

/-! ## Coproducts of quasi-isomorphisms -/

/-- A coproduct of quasi-isomorphisms of cochain complexes is a quasi-isomorphism.  This is
the coproduct case of `Work.TOOLKIT.Coprod.quasiIso_colimMap` (the shape is `Discrete J`, where
`colimMap` is `Limits.Sigma.map`). -/
private theorem quasiIso_sigmaMap {J : Type} (K L : J → Work.TOOLKIT.Cpx)
    [HasCoproduct K] [HasCoproduct L]
    (f : ∀ j, K j ⟶ L j) (hf : ∀ j, QuasiIso (f j)) :
    QuasiIso (Limits.Sigma.map f) := by
  have : HasColimitsOfShape (Discrete J) LightCondAb := inferInstance
  have : HasExactColimitsOfShape (Discrete J) LightCondAb := inferInstance
  refine quasiIso_colimMap (F := Discrete.functor K) (G := Discrete.functor L)
    (Discrete.natTrans (fun j : Discrete J => f j.as)) ?_
  intro j
  simpa using hf j.as

/-! ## Lifting the two kinds of fractions -/

/-- If a morphism `h` of the homotopy category becomes zero in the derived category, then it can
be killed on the left by a quasi-isomorphism: there are `t : X ⟶ A` with `QuasiIso t` and
`qF.map t ≫ h = 0`.  This is `MorphismProperty.map_eq_iff_precomp` together with the fact that
the quotient functor is full and essentially surjective. -/
private lemma exists_quasiIso_comp_eq_zero {A B : Work.TOOLKIT.Cpx}
    (h : qF.obj A ⟶ qF.obj B) (hh : DerivedCategory.Qh.map h = 0) :
    ∃ (X : Work.TOOLKIT.Cpx) (t : X ⟶ A), QuasiIso t ∧ qF.map t ≫ h = 0 := by
  obtain ⟨X', σ, hσ, hzero⟩ :=
    (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh wq h 0).1 (by simpa using hh)
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨t, rfl⟩ := qF.map_surjective σ
  exact ⟨X, t, (HomotopyCategory.quotient_map_mem_quasiIso_iff t).1 hσ, by simpa using hzero⟩

/-- A morphism `Qh (qF A) ⟶ Qh (qF B)` is a right fraction `inv (Qh s) ≫ Qh γ` with `s` a
quasi-isomorphism, and both `s` and `γ` can be lifted to chain maps.  The equation is recorded in
the "cancelled" form `Qh s ≫ x = Qh γ`, which is what the surjectivity construction needs. -/
private lemma exists_rightFraction_lift {A B : Work.TOOLKIT.Cpx}
    (x : DerivedCategory.Qh.obj (qF.obj A) ⟶ DerivedCategory.Qh.obj (qF.obj B)) :
    ∃ (X : Work.TOOLKIT.Cpx) (s : X ⟶ A) (γ : X ⟶ B), QuasiIso s ∧
      DerivedCategory.Qh.map (qF.map s) ≫ x = DerivedCategory.Qh.map (qF.map γ) := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction DerivedCategory.Qh wq x
  obtain ⟨X', s, hs, f, rfl⟩ := φ.cases
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := qF.map_surjective s
  obtain ⟨γ, rfl⟩ := qF.map_surjective f
  haveI : IsIso (DerivedCategory.Qh.map (qF.map s)) :=
    (DerivedCategory.isIso_Qh_map_iff (qF.map s)).2 hs
  refine ⟨X, s, γ, (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs, ?_⟩
  rw [hφ]
  exact IsIso.hom_inv_id_assoc (DerivedCategory.Qh.map (qF.map s))
    (DerivedCategory.Qh.map (qF.map γ))

/-! ## The main theorem -/

/-- The localization `Qh : K(LightCondAb) ⟶ D(LightCondAb)` of the homotopy category at the
quasi-isomorphisms preserves small coproducts: for every `Z` in the derived category, the
canonical map `Hom_D(Qh (hq (∐ K)), Z) → ∏ j, Hom_D(Qh (hq (K j)), Z)` is a bijection.
Route (uses both calculi of fractions).
Injectivity: reduce to `ψ` with `Qh (ι j) ≫ ψ = 0` for all `j`; a left fraction
(`DerivedCategory.left_fac`) gives `ψ = Qh g ≫ inv (Qh t)` with `t` a quasi-isomorphism, hence
`Qh (ι j ≫ g) = 0`; by `MorphismProperty.map_eq_iff_precomp` there are `s j : X'_j ⟶ K j` with
`Qh (s j)` an iso and `s j ≫ ι j ≫ g = 0` in `K`; choose chain maps `σ j` hitting the `s j`, then
`∐ σ j` is a quasi-isomorphism (coproducts of quasi-isomorphisms), each component of
`hq (∐ σ) ≫ g` is zero in `K`, so `hq (∐ σ) ≫ g = 0` by the homotopy-category statement
`hq_sigma_bijective`; as `Qh (hq (∐ σ))` is an isomorphism, `Qh g = 0` and `ψ = 0`.
Surjectivity: right fractions (`DerivedCategory.right_fac`) `φ j = inv (Qh (s j)) ≫ Qh (γ j)`
with `s j` a quasi-isomorphism; set `φ := inv (Q (∐ s j)) ≫ Q (Sigma.desc (fun j => γ j))`, using
that `∐ s j` is a quasi-isomorphism and `Sigma.ι_comp_map`.
For `Z` not in the image of `Qh`, use that `Qh` is essentially surjective. -/
theorem Qh_sigma_bijective (J : Type) (K : J → Work.TOOLKIT.Cpx)
    [CategoryTheory.Limits.HasCoproduct K] (Z : Work.TOOLKIT.DCat) :
    Function.Bijective (fun (φ : DerivedCategory.Qh.obj ((HomotopyCategory.quotient
        LightCondAb (ComplexShape.up ℤ)).obj
        (CategoryTheory.Limits.sigmaObj K)) ⟶ Z) (j : J) =>
      CategoryTheory.CategoryStruct.comp (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map
          (CategoryTheory.Limits.Sigma.ι K j))) φ) := by
  -- It suffices to prove the statement for targets in the image of `Qh`.
  have key : ∀ Y : Work.TOOLKIT.KCat, Function.Bijective
      (fun (φ : DerivedCategory.Qh.obj (qF.obj (∐K)) ⟶ DerivedCategory.Qh.obj Y) (j : J) =>
        DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) ≫ φ) := by
    intro Y
    obtain ⟨Y', rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    constructor
    · -- injectivity
      intro φ ψ hφψ
      -- a morphism all of whose components vanish is zero
      have hkey : ∀ θ : DerivedCategory.Qh.obj (qF.obj (∐K)) ⟶
            DerivedCategory.Qh.obj (qF.obj Y'),
          (∀ j, DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) ≫ θ = 0) → θ = 0 := by
        intro θ hθ
        -- write `θ` as a left fraction `Qh g ≫ inv (Qh t')`
        obtain ⟨φl, hψl⟩ := Localization.exists_leftFraction DerivedCategory.Qh wq θ
        obtain ⟨Y'', g, t', ht', rfl⟩ := φl.cases
        haveI : IsIso (DerivedCategory.Qh.map t') :=
          (DerivedCategory.isIso_Qh_map_iff t').2 ht'
        have hfac : θ = DerivedCategory.Qh.map g ≫ inv (DerivedCategory.Qh.map t') := hψl
        -- each `Qh (ι j ≫ g)` vanishes
        have hq : ∀ j, DerivedCategory.Qh.map (qF.map (Sigma.ι K j) ≫ g) = 0 := by
          intro j
          have h1 : DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) ≫
              (DerivedCategory.Qh.map g ≫ inv (DerivedCategory.Qh.map t')) = 0 := by
            simpa only [hfac] using hθ j
          rw [← Category.assoc, ← Functor.map_comp] at h1
          have h2 := congrArg (fun u => u ≫ DerivedCategory.Qh.map t') h1
          simpa [Category.assoc] using h2
        -- kill each `ι j ≫ g` by a quasi-isomorphism, and lift it to chain maps
        choose X'' t ht hz using fun j =>
          exists_quasiIso_comp_eq_zero (qF.map (Sigma.ι K j) ≫ g) (hq j)
        letI : HasCoproduct X'' := inferInstance
        -- the coproduct of the quasi-isomorphisms kills `g`
        have hT0 : qF.map (Limits.Sigma.map t) ≫ g = 0 := by
          refine (hq_sigma_bijective J X'' Y'').1 (funext fun j => ?_)
          have hcomp : qF.map (Sigma.ι X'' j) ≫
              (qF.map (Limits.Sigma.map t) ≫ g) = 0 := by
            have h1 : qF.map (Sigma.ι X'' j) ≫ qF.map (Limits.Sigma.map t) =
                qF.map (t j) ≫ qF.map (Sigma.ι K j) := by
              rw [← qF.map_comp, ← qF.map_comp, Sigma.ι_map]
            rw [← Category.assoc, h1, Category.assoc]
            exact hz j
          simp only [hcomp, comp_zero]
        have hqiT : QuasiIso (Limits.Sigma.map t) :=
          quasiIso_sigmaMap X'' K t (fun j => ht j)
        haveI : IsIso (DerivedCategory.Qh.map (qF.map (Limits.Sigma.map t))) := by
          rw [DerivedCategory.isIso_Qh_map_iff]
          exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (Limits.Sigma.map t)).2 hqiT
        have hQg : DerivedCategory.Qh.map g = 0 := by
          have h1 : DerivedCategory.Qh.map (qF.map (Limits.Sigma.map t)) ≫
              DerivedCategory.Qh.map g = 0 := by
            rw [← DerivedCategory.Qh.map_comp, hT0, DerivedCategory.Qh.map_zero]
          have h2 := congrArg (fun u => inv (DerivedCategory.Qh.map
            (qF.map (Limits.Sigma.map t))) ≫ u) h1
          simpa [Category.assoc] using h2
        rw [hfac, hQg, zero_comp]
      have hsub : ∀ j, DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) ≫ (φ - ψ) = 0 := by
        intro j
        rw [Preadditive.comp_sub, sub_eq_zero]
        exact congrFun hφψ j
      exact sub_eq_zero.mp (hkey (φ - ψ) hsub)
    · -- surjectivity
      intro v
      -- write each component as a right fraction and lift the fraction to chain maps
      choose X'' s γ hs hsx using fun j => exists_rightFraction_lift (v j)
      letI : HasCoproduct X'' := inferInstance
      haveI : IsIso (DerivedCategory.Qh.map (qF.map (Limits.Sigma.map s))) := by
        rw [DerivedCategory.isIso_Qh_map_iff]
        exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (Limits.Sigma.map s)).2
          (quasiIso_sigmaMap X'' K s hs)
      refine ⟨inv (DerivedCategory.Qh.map (qF.map (Limits.Sigma.map s))) ≫
        DerivedCategory.Qh.map (qF.map (Limits.Sigma.desc (fun j => γ j))), ?_⟩
      funext j
      haveI : IsIso (DerivedCategory.Qh.map (qF.map (s j))) := by
        rw [DerivedCategory.isIso_Qh_map_iff]
        exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (s j)).2 (hs j)
      -- the component of `∐ s` at `j` is `s j`, so the inverse of `Qh (∐ s)` commutes with the
      -- coprojections
      have hstep : DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) ≫
          inv (DerivedCategory.Qh.map (qF.map (Limits.Sigma.map s))) =
          inv (DerivedCategory.Qh.map (qF.map (s j))) ≫
            DerivedCategory.Qh.map (qF.map (Sigma.ι X'' j)) := by
        have h2 : DerivedCategory.Qh.map (qF.map (Sigma.ι X'' j)) ≫
            DerivedCategory.Qh.map (qF.map (Limits.Sigma.map s)) =
            DerivedCategory.Qh.map (qF.map (s j)) ≫
              DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) := by
          rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp,
            ← qF.map_comp, ← qF.map_comp, Sigma.ι_map]
        have h3 : DerivedCategory.Qh.map (qF.map (s j)) ≫
            (DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) ≫
              inv (DerivedCategory.Qh.map (qF.map (Limits.Sigma.map s)))) =
            DerivedCategory.Qh.map (qF.map (Sigma.ι X'' j)) := by
          rw [← Category.assoc, ← h2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        rw [← cancel_epi (DerivedCategory.Qh.map (qF.map (s j))), h3,
          IsIso.hom_inv_id_assoc]
      -- the component of `Sigma.desc γ` at `j` is `γ j`
      have hlast : DerivedCategory.Qh.map (qF.map (Sigma.ι X'' j)) ≫
          DerivedCategory.Qh.map (qF.map (Limits.Sigma.desc (fun j => γ j))) =
          DerivedCategory.Qh.map (qF.map (γ j)) := by
        rw [← DerivedCategory.Qh.map_comp, ← qF.map_comp, Sigma.ι_comp_desc]
      calc DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) ≫
            (inv (DerivedCategory.Qh.map (qF.map (Limits.Sigma.map s))) ≫
              DerivedCategory.Qh.map (qF.map (Limits.Sigma.desc (fun j => γ j))))
          = (DerivedCategory.Qh.map (qF.map (Sigma.ι K j)) ≫
              inv (DerivedCategory.Qh.map (qF.map (Limits.Sigma.map s)))) ≫
              DerivedCategory.Qh.map (qF.map (Limits.Sigma.desc (fun j => γ j))) := by
            rw [Category.assoc]
        _ = (inv (DerivedCategory.Qh.map (qF.map (s j))) ≫
              DerivedCategory.Qh.map (qF.map (Sigma.ι X'' j))) ≫
              DerivedCategory.Qh.map (qF.map (Limits.Sigma.desc (fun j => γ j))) := by
            rw [hstep]
        _ = inv (DerivedCategory.Qh.map (qF.map (s j))) ≫
              (DerivedCategory.Qh.map (qF.map (Sigma.ι X'' j)) ≫
                DerivedCategory.Qh.map (qF.map (Limits.Sigma.desc (fun j => γ j)))) := by
            rw [Category.assoc]
        _ = inv (DerivedCategory.Qh.map (qF.map (s j))) ≫
              DerivedCategory.Qh.map (qF.map (γ j)) := by rw [hlast]
        _ = v j := by
          rw [← hsx j, IsIso.inv_hom_id_assoc]
  -- reduce an arbitrary target to a target in the image of `Qh`
  let Y := DerivedCategory.Qh.objPreimage Z
  let e := DerivedCategory.Qh.objObjPreimageIso Z
  exact (bijective_conj_target (fun j => DerivedCategory.Qh.map (qF.map (Sigma.ι K j))) e).1
    (key Y)

end Work.TOOLKIT.Coprod
