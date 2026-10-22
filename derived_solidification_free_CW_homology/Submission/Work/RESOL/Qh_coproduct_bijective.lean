import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.SigmaSetup
import Submission.Work.RESOL.Instances
import Submission.Work.RESOL.hq_coproduct
import Submission.Work.TOOLKIT.Coprod.quasiIso_colimMap

/-!
AREA RESOL — `Qh` preserves small coproducts.

For a family `K : J → Cpx` with a coproduct, the localization
`Qh : K(LightCondAb) ⤳ D(LightCondAb)` of the homotopy category at the quasi-isomorphisms
sends the coproduct cocone `(hq (∐ K), hq (ι j))` to a colimit cocone: for every complex `X`,
the canonical map

`Hom_D (Qh (hq (∐ K)), Qh (hq X)) ⟶ ∏ j, Hom_D (Qh (hq (K j)), Qh (hq X))`,
`φ ↦ (Qh (hq (ι j)) ≫ φ) j`

is a bijection (`Qh_coproduct_bijective`).

The proof uses the two calculi of fractions for the quasi-isomorphisms of the homotopy
category (`MorphismProperty.map_eq_iff_precomp`, `Localization.exists_leftFraction`,
`Localization.exists_rightFraction`):

* *surjectivity*: a morphism `Qh (hq (K j)) ⟶ Qh (hq X)` is a right fraction
  `inv (Q (s j)) ≫ Q (b j)` with `s j` a quasi-isomorphism (`DerivedCategory.right_fac`);
  the coproduct `T := ∐ j, s j` of the denominators is again a quasi-isomorphism
  (`quasiIso_sigma_map`, from `Work.TOOLKIT.Coprod.quasiIso_colimMap`), and
  `inv (Q T) ≫ Q (Sigma.desc b)` has the prescribed components (`Sigma.ι_map`,
  `Sigma.ι_comp_desc`).
* *injectivity*: a morphism `F` with vanishing components is a left fraction
  `Q g ≫ inv (Q s)` (`DerivedCategory.left_fac`), so `Q (ι j ≫ g) = 0` for all `j`; by
  `map_eq_iff_precomp` there are quasi-isomorphisms `t j : K' j ⟶ K j` with `t j ≫ ι j ≫ g`
  null-homotopic.  Since `∐ j, t j` is a quasi-isomorphism and all its components are
  null-homotopic, `homotopy_of_components` shows `Q (∐ t j) ≫ Q g = 0`, whence `Q g = 0`.

The statement is phrased for `Qh ∘ hq`; the auxiliary statement for `Q` alone is
`Q_coproduct_bijective`, and `Qh_coproduct_bijective` is deduced from it by conjugating with
the isomorphism `DerivedCategory.quotientCompQhIso : hq ⋙ Qh ≅ Q`.
-/
open CategoryTheory Limits LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.RESOL

/-- The class of quasi-isomorphisms in the homotopy category `K(LightCondAb)`. -/
private abbrev qisoClass : MorphismProperty KCat :=
  HomotopyCategory.quasiIso LightCondAb (ComplexShape.up ℤ)

/-- The component of the isomorphism `hq ⋙ Qh ≅ Q` at a cochain complex. -/
private noncomputable abbrev qhQApp (Y : Cpx) :
    DerivedCategory.Qh.obj (qF.obj Y) ≅ DerivedCategory.Q.obj Y :=
  (DerivedCategory.quotientCompQhIso LightCondAb).app Y

/-! ## Coproducts of quasi-isomorphisms -/

/-- **Coproducts of quasi-isomorphisms are quasi-isomorphisms.**  This is the instance
`J = Discrete J'` of `Work.TOOLKIT.Coprod.quasiIso_colimMap`. -/
theorem quasiIso_sigma_map {J : Type} (K L : J → Cpx) [HasCoproduct K] [HasCoproduct L]
    (f : ∀ j, K j ⟶ L j) (hf : ∀ j, QuasiIso (f j)) : QuasiIso (Limits.Sigma.map f) := by
  have h := Work.TOOLKIT.Coprod.quasiIso_colimMap (J := Discrete J)
    (F := Discrete.functor K) (G := Discrete.functor L)
    (Discrete.natTrans (F := Discrete.functor K) (G := Discrete.functor L)
      (fun j => f j.as)) (fun j => hf j.as)
  have heq : colimMap (Discrete.natTrans (F := Discrete.functor K) (G := Discrete.functor L)
        (fun j : Discrete J => f j.as)) = Limits.Sigma.map f := by
    apply Sigma.hom_ext
    intro j
    calc Sigma.ι K j ≫ colimMap (Discrete.natTrans (F := Discrete.functor K)
            (G := Discrete.functor L) (fun j : Discrete J => f j.as))
        = (Discrete.natTrans (F := Discrete.functor K) (G := Discrete.functor L)
            (fun j : Discrete J => f j.as)).app (Discrete.mk j) ≫ Sigma.ι L j := ι_colimMap _ _
      _ = f j ≫ Sigma.ι L j := rfl
      _ = Sigma.ι K j ≫ Limits.Sigma.map f := (Sigma.ι_map f j).symm
  rwa [heq] at h

/-! ## The statement for `Q` alone -/

/-- A chain map which is zero in the derived category can be killed up to homotopy by a
quasi-isomorphism.  This is the criterion `MorphismProperty.map_eq_iff_precomp` for the
localization `Qh` of the homotopy category, transported through the isomorphism `hq ⋙ Qh ≅ Q`. -/
private lemma exists_quasiIso_homotopy_of_Q_map_eq_zero {K L : Cpx} (k : K ⟶ L)
    (hk : DerivedCategory.Q.map k = 0) :
    ∃ (K' : Cpx) (t : K' ⟶ K), QuasiIso t ∧ Nonempty (Homotopy (t ≫ k) 0) := by
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality (C := LightCondAb) k
  have hq : DerivedCategory.Qh.map (qF.map k) = 0 := by
    have h1 : DerivedCategory.Qh.map (qF.map k) ≫ (qhQApp L).hom = 0 := by
      show DerivedCategory.Qh.map (qF.map k) ≫
        (DerivedCategory.quotientCompQhIso LightCondAb).hom.app L = 0
      rw [hnat, hk, comp_zero]
    calc DerivedCategory.Qh.map (qF.map k)
        = (DerivedCategory.Qh.map (qF.map k) ≫ (qhQApp L).hom) ≫ (qhQApp L).inv := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = 0 := by rw [h1, zero_comp]
  obtain ⟨Z, t, ht, hcomp⟩ :=
    (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh qisoClass (qF.map k) 0).1
      (by rw [hq]; simp)
  obtain ⟨K', rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨t', ht'⟩ := (HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map_surjective t
  have htq : QuasiIso t' :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff t').1 (by rw [ht']; exact ht)
  refine ⟨K', t', htq, ?_⟩
  have h1 : qF.map (t' ≫ k) = 0 := by
    rw [Functor.map_comp, ht']
    simpa using hcomp
  exact (HomotopyCategory.quotient_map_eq_zero_iff (t' ≫ k)).1 h1

/-- **`Q` preserves small coproducts.**  For a family of complexes `K` and a complex `X`, the
canonical map `Hom_D (Q (∐ K), Q X) ⟶ ∏ j, Hom_D (Q (K j), Q X)`, `φ ↦ (Q (ι j) ≫ φ) j`,
is a bijection. -/
theorem Q_coproduct_bijective {J : Type} (K : J → Cpx) [HasCoproduct K] (X : Cpx) :
    Function.Bijective (fun g : DerivedCategory.Q.obj (∐K) ⟶ DerivedCategory.Q.obj X =>
      fun j => DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ g) := by
  constructor
  · intro F F' hFF
    have key : ∀ F : DerivedCategory.Q.obj (∐K) ⟶ DerivedCategory.Q.obj X,
        (∀ j, DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ F = 0) → F = 0 := by
      intro F hF
      obtain ⟨Y', g, s, hs, hfac⟩ := DerivedCategory.left_fac F
      haveI : IsIso (DerivedCategory.Q.map s) := hs
      have hcancel : F ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map g := by
        rw [hfac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      have hk : ∀ j, DerivedCategory.Q.map (Limits.Sigma.ι K j ≫ g) = 0 := fun j => by
        calc DerivedCategory.Q.map (Limits.Sigma.ι K j ≫ g)
            = DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ DerivedCategory.Q.map g :=
              Functor.map_comp _ _ _
          _ = DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ (F ≫ DerivedCategory.Q.map s) := by
              rw [hcancel]
          _ = (DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ F) ≫ DerivedCategory.Q.map s :=
              (Category.assoc _ _ _).symm
          _ = 0 := by rw [hF j, zero_comp]
      choose K' t hrest using fun j =>
        exists_quasiIso_homotopy_of_Q_map_eq_zero (Limits.Sigma.ι K j ≫ g) (hk j)
      have ht : ∀ j, QuasiIso (t j) := fun j => (hrest j).1
      have hhom : ∀ j, Nonempty (Homotopy (t j ≫ (Limits.Sigma.ι K j ≫ g)) 0) := fun j =>
        (hrest j).2
      haveI : HasCoproduct K' := inferInstance
      have hT : QuasiIso (Limits.Sigma.map t) := quasiIso_sigma_map K' K t ht
      have hcomp : ∀ j, Homotopy (Limits.Sigma.ι K' j ≫ (Limits.Sigma.map t ≫ g)) 0 := fun j => by
        have h1 : Limits.Sigma.ι K' j ≫ (Limits.Sigma.map t ≫ g) =
            t j ≫ (Limits.Sigma.ι K j ≫ g) := by
          rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc]
        rw [h1]
        exact (hhom j).some
      have hTg : Homotopy (Limits.Sigma.map t ≫ g) 0 := homotopy_of_components K' _ hcomp
      have hzero : DerivedCategory.Q.map (Limits.Sigma.map t ≫ g) = 0 := by
        rw [DerivedCategory.Q_map_eq_of_homotopy (C := LightCondAb) hTg]
        simp
      haveI : IsIso (DerivedCategory.Q.map (Limits.Sigma.map t)) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso (C := LightCondAb) (Limits.Sigma.map t)).2 hT
      have hg0 : DerivedCategory.Q.map g = 0 := by
        have h1 : DerivedCategory.Q.map (Limits.Sigma.map t) ≫ DerivedCategory.Q.map g = 0 := by
          rw [← Functor.map_comp, hzero]
        calc DerivedCategory.Q.map g
            = inv (DerivedCategory.Q.map (Limits.Sigma.map t)) ≫
                (DerivedCategory.Q.map (Limits.Sigma.map t) ≫ DerivedCategory.Q.map g) := by
              rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
          _ = 0 := by rw [h1, comp_zero]
      rw [hfac, hg0, zero_comp]
    have hsub : ∀ j, DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ (F - F') = 0 := fun j => by
      rw [Preadditive.comp_sub, sub_eq_zero]
      exact congrFun hFF j
    exact sub_eq_zero.mp (key (F - F') hsub)
  · intro v
    choose K' s hs b hfac using fun j => DerivedCategory.right_fac (v j)
    haveI : HasCoproduct K' := inferInstance
    have hsQ : ∀ j, QuasiIso (s j) := fun j =>
      (DerivedCategory.isIso_Q_map_iff_quasiIso (C := LightCondAb) (s j)).1 (hs j)
    have hS : QuasiIso (Limits.Sigma.map s) := quasiIso_sigma_map K' K s hsQ
    haveI : IsIso (DerivedCategory.Q.map (Limits.Sigma.map s)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (C := LightCondAb) (Limits.Sigma.map s)).2 hS
    refine ⟨inv (DerivedCategory.Q.map (Limits.Sigma.map s)) ≫
      DerivedCategory.Q.map (Limits.Sigma.desc b), ?_⟩
    funext j
    haveI : IsIso (DerivedCategory.Q.map (s j)) := hs j
    have h2 : DerivedCategory.Q.map (Limits.Sigma.ι K' j) ≫
        DerivedCategory.Q.map (Limits.Sigma.map s) =
        DerivedCategory.Q.map (s j) ≫ DerivedCategory.Q.map (Limits.Sigma.ι K j) := by
      rw [← Functor.map_comp, ← Functor.map_comp, Limits.Sigma.ι_map s j]
    have h3 : DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫
        inv (DerivedCategory.Q.map (Limits.Sigma.map s)) =
        inv (DerivedCategory.Q.map (s j)) ≫ DerivedCategory.Q.map (Limits.Sigma.ι K' j) := by
      have key : (inv (DerivedCategory.Q.map (s j)) ≫ DerivedCategory.Q.map (Limits.Sigma.ι K' j))
            ≫ DerivedCategory.Q.map (Limits.Sigma.map s) =
          DerivedCategory.Q.map (Limits.Sigma.ι K j) := by
        rw [Category.assoc, h2, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      calc DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫
            inv (DerivedCategory.Q.map (Limits.Sigma.map s))
          = ((inv (DerivedCategory.Q.map (s j)) ≫ DerivedCategory.Q.map (Limits.Sigma.ι K' j)) ≫
              DerivedCategory.Q.map (Limits.Sigma.map s)) ≫
                inv (DerivedCategory.Q.map (Limits.Sigma.map s)) := by rw [key]
        _ = inv (DerivedCategory.Q.map (s j)) ≫ DerivedCategory.Q.map (Limits.Sigma.ι K' j) := by
            rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have hbj : DerivedCategory.Q.map (Limits.Sigma.ι K' j) ≫
        DerivedCategory.Q.map (Limits.Sigma.desc b) = DerivedCategory.Q.map (b j) := by
      rw [← Functor.map_comp, Limits.Sigma.ι_comp_desc]
    calc DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫
          (inv (DerivedCategory.Q.map (Limits.Sigma.map s)) ≫
            DerivedCategory.Q.map (Limits.Sigma.desc b))
        = (DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫
            inv (DerivedCategory.Q.map (Limits.Sigma.map s))) ≫
              DerivedCategory.Q.map (Limits.Sigma.desc b) := (Category.assoc _ _ _).symm
      _ = (inv (DerivedCategory.Q.map (s j)) ≫ DerivedCategory.Q.map (Limits.Sigma.ι K' j)) ≫
              DerivedCategory.Q.map (Limits.Sigma.desc b) := by rw [h3]
      _ = inv (DerivedCategory.Q.map (s j)) ≫
              (DerivedCategory.Q.map (Limits.Sigma.ι K' j) ≫
                DerivedCategory.Q.map (Limits.Sigma.desc b)) := Category.assoc _ _ _
      _ = inv (DerivedCategory.Q.map (s j)) ≫ DerivedCategory.Q.map (b j) := by rw [hbj]
      _ = v j := (hfac j).symm

/-! ## The statement for `Qh` -/

/-- The componentwise comparison of `Qh (hq (ι j))` and `Q (ι j)`: both are conjugated by the
isomorphisms `DerivedCategory.quotientCompQhIso`. -/
private lemma Qh_coproduct_bijective_rel {J : Type} (K : J → Cpx) (j : J) :
    DerivedCategory.Q.map (Limits.Sigma.ι K j) =
      (qhQApp (K j)).inv ≫ DerivedCategory.Qh.map (qF.map (Limits.Sigma.ι K j)) ≫
        (qhQApp (∐K)).hom := by
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality (C := LightCondAb)
    (Limits.Sigma.ι K j)
  have hnat' : (qhQApp (K j)).hom ≫ DerivedCategory.Q.map (Limits.Sigma.ι K j) =
      DerivedCategory.Qh.map (qF.map (Limits.Sigma.ι K j)) ≫ (qhQApp (∐K)).hom := hnat
  calc DerivedCategory.Q.map (Limits.Sigma.ι K j)
      = (qhQApp (K j)).inv ≫ ((qhQApp (K j)).hom ≫
          DerivedCategory.Q.map (Limits.Sigma.ι K j)) := by
        rw [Iso.inv_hom_id_assoc]
    _ = (qhQApp (K j)).inv ≫
          (DerivedCategory.Qh.map (qF.map (Limits.Sigma.ι K j)) ≫ (qhQApp (∐K)).hom) := by
        rw [← hnat']
    _ = (qhQApp (K j)).inv ≫ DerivedCategory.Qh.map (qF.map (Limits.Sigma.ι K j)) ≫
          (qhQApp (∐K)).hom := rfl

theorem Qh_coproduct_bijective {J : Type} (K : J → Work.RESOL.Cpx)
    [CategoryTheory.Limits.HasCoproduct K] (X : Work.RESOL.Cpx) :
    Function.Bijective (fun h : Quiver.Hom
        (DerivedCategory.Qh.obj (Work.RESOL.qF.obj (CategoryTheory.Limits.sigmaObj K)))
        (DerivedCategory.Qh.obj (Work.RESOL.qF.obj X)) =>
      fun j => CategoryTheory.CategoryStruct.comp
        (DerivedCategory.Qh.map (Work.RESOL.qF.map (CategoryTheory.Limits.Sigma.ι K j))) h)
    := by
  let Φ : (DerivedCategory.Qh.obj (qF.obj (∐K)) ⟶ DerivedCategory.Qh.obj (qF.obj X)) →
      ((j : J) → DerivedCategory.Qh.obj (qF.obj (K j)) ⟶ DerivedCategory.Qh.obj (qF.obj X)) :=
    fun h j => DerivedCategory.Qh.map (qF.map (Limits.Sigma.ι K j)) ≫ h
  let B : (DerivedCategory.Qh.obj (qF.obj (∐K)) ⟶ DerivedCategory.Qh.obj (qF.obj X)) →
      (DerivedCategory.Q.obj (∐K) ⟶ DerivedCategory.Q.obj X) :=
    fun h => (qhQApp (∐K)).inv ≫ h
  let A : ((j : J) → DerivedCategory.Qh.obj (qF.obj (K j)) ⟶ DerivedCategory.Qh.obj (qF.obj X)) →
      ((j : J) → DerivedCategory.Q.obj (K j) ⟶ DerivedCategory.Q.obj X) :=
    fun v j => (qhQApp (K j)).hom ≫ v j
  let Ψ : (DerivedCategory.Q.obj (∐K) ⟶ DerivedCategory.Q.obj X) →
      ((j : J) → DerivedCategory.Q.obj (K j) ⟶ DerivedCategory.Q.obj X) :=
    fun g j => DerivedCategory.Q.map (Limits.Sigma.ι K j) ≫ g
  have hB : Function.Bijective B := by
    refine ⟨fun h₁ h₂ hh => ?_, fun g => ⟨(qhQApp (∐K)).hom ≫ g, ?_⟩⟩
    · have h' := congrArg (fun t => (qhQApp (∐K)).hom ≫ t) hh
      dsimp only [B] at h'
      simpa only [Iso.hom_inv_id_assoc] using h'
    · dsimp only [B]
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hA : Function.Bijective A := by
    refine ⟨fun v₁ v₂ hv => ?_, fun w => ⟨fun j => (qhQApp (K j)).inv ≫ w j, ?_⟩⟩
    · funext j
      have h' := congrArg (fun t => (qhQApp (K j)).inv ≫ t) (congrFun hv j)
      dsimp only [A] at h'
      simpa only [Iso.inv_hom_id_assoc] using h'
    · funext j
      dsimp only [A]
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hΨ : Function.Bijective Ψ := Q_coproduct_bijective K X
  have hΦeq : Φ = fun h => A (Ψ (B h)) := by
    funext h j
    dsimp only [Φ, B, A, Ψ]
    rw [Qh_coproduct_bijective_rel K j]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change Function.Bijective Φ
  rw [hΦeq]
  exact hA.comp (hΨ.comp hB)

end Work.RESOL
