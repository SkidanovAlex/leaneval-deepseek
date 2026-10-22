import Mathlib
import Submission.Work.ANALYTIC.CechPt.cech_h0

/-!
# Čech descent in degree `0` for an arbitrary light condensed source

For `β : X ⟶ Y` an epimorphism of light condensed sets with `X` an *arbitrary* light condensed
set (no profiniteness assumption), the augmentation of the `ℤ[-]`-Čech complex induces an
isomorphism on degree-`0` homology.  Equivalently, the cofork

  `ℤ[X ×_Y X] ⇉ ℤ[X] ⟶ ℤ[Y]`

is a colimit.

This is the generalisation of `Work.ANALYTIC.CechPt.cech_h0`, whose proof never used
profiniteness of the source beyond the binder type of `β`: every substantive step uses only the
`WidePullback` description of the Čech nerve, the effective-epimorphism structure of `β`, and the
free/forget adjunction.  Accordingly the same definitions are re-stated here for an arbitrary
`X : LightCondSet` and the proofs carry over verbatim.
-/

namespace Work.ANALYTIC.CechLight

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open AlgebraicTopology

noncomputable section

variable {X : LightCondSet.{0}} {Y : LightCondSet.{0}}

/-! ## §1. The bottom of the Čech nerve -/

/-- The Čech nerve of a map of light condensed sets, as a simplicial object. -/
noncomputable abbrev lcechNerve (β : X ⟶ Y) : SimplicialObject LightCondSet.{0} :=
  Arrow.cechNerve (Arrow.mk β)

/-- The level-`0` term of the Čech nerve of `β`, i.e. the wide pullback of one copy of `X`
over `Y`. -/
noncomputable abbrev lcw1 (β : X ⟶ Y) : LightCondSet :=
  Limits.widePullback Y (fun _ : Fin 1 => X) (fun _ => β)

/-- The level-`1` term of the Čech nerve of `β`, i.e. the wide pullback of two copies of `X`
over `Y` (`X ×_Y X`). -/
noncomputable abbrev lcw2 (β : X ⟶ Y) : LightCondSet :=
  Limits.widePullback Y (fun _ : Fin 2 => X) (fun _ => β)

/-- The `j`-th projection of the level-`0` term. -/
noncomputable abbrev lcpi1 (β : X ⟶ Y) (j : Fin 1) : lcw1 β ⟶ X :=
  Limits.WidePullback.π (fun _ : Fin 1 => β) j

/-- The structure map of the level-`0` term. -/
noncomputable abbrev lcbase1 (β : X ⟶ Y) : lcw1 β ⟶ Y :=
  Limits.WidePullback.base (fun _ : Fin 1 => β)

/-- The `j`-th projection of the level-`1` term. -/
noncomputable abbrev lcpi2 (β : X ⟶ Y) (j : Fin 2) : lcw2 β ⟶ X :=
  Limits.WidePullback.π (fun _ : Fin 2 => β) j

/-- The structure map of the level-`1` term. -/
noncomputable abbrev lcbase2 (β : X ⟶ Y) : lcw2 β ⟶ Y :=
  Limits.WidePullback.base (fun _ : Fin 2 => β)

lemma lcpi1_comp (β : X ⟶ Y) : lcpi1 β 0 ≫ β = lcbase1 β :=
  Limits.WidePullback.π_arrow _ _

lemma lcpi2_comp (β : X ⟶ Y) (j : Fin 2) : lcpi2 β j ≫ β = lcbase2 β :=
  Limits.WidePullback.π_arrow _ _

/-- The face map `δ₀` at the bottom of the Čech nerve, as a map `X ×_Y X ⟶ X`. -/
noncomputable abbrev lcdelta0 (β : X ⟶ Y) : lcw2 β ⟶ lcw1 β :=
  Limits.WidePullback.lift (lcbase2 β) (fun _ : Fin 1 => lcpi2 β 1)
    (by intro j; exact lcpi2_comp β 1)

/-- The face map `δ₁` at the bottom of the Čech nerve, as a map `X ×_Y X ⟶ X`. -/
noncomputable abbrev lcdelta1 (β : X ⟶ Y) : lcw2 β ⟶ lcw1 β :=
  Limits.WidePullback.lift (lcbase2 β) (fun _ : Fin 1 => lcpi2 β 0)
    (by intro j; exact lcpi2_comp β 0)

lemma lcdelta0_comp_pi1 (β : X ⟶ Y) : lcdelta0 β ≫ lcpi1 β 0 = lcpi2 β 1 :=
  Limits.WidePullback.lift_π _ _ _ _ _

lemma lcdelta1_comp_pi1 (β : X ⟶ Y) : lcdelta1 β ≫ lcpi1 β 0 = lcpi2 β 0 :=
  Limits.WidePullback.lift_π _ _ _ _ _

lemma lcdelta0_comp_base (β : X ⟶ Y) : lcdelta0 β ≫ lcbase1 β = lcbase2 β :=
  Limits.WidePullback.lift_base _ _ _ _

lemma lcdelta1_comp_base (β : X ⟶ Y) : lcdelta1 β ≫ lcbase1 β = lcbase2 β :=
  Limits.WidePullback.lift_base _ _ _ _

/-- The face map `δ i` of the Čech nerve, composed with the identification of the level-`0` term
with `X`, is the `i`-th projection of the wide pullback `X ×_Y X`. -/
lemma cechNerve_delta_comp_pi1 (β : X ⟶ Y) (i : Fin 2) :
    (lcechNerve β).δ i ≫ Limits.WidePullback.π (fun _ : Fin 1 => β) (0 : Fin 1) =
      Limits.WidePullback.π (fun _ : Fin 2 => β) (Fin.succAbove i 0) := by
  change Limits.WidePullback.lift (Limits.WidePullback.base (fun _ : Fin 2 => β))
      (fun j : Fin 1 => Limits.WidePullback.π (fun _ : Fin 2 => β)
        ((SimplexCategory.δ i).toOrderHom j)) (by simp)
    ≫ Limits.WidePullback.π (fun _ : Fin 1 => β) 0 = _
  rw [Limits.WidePullback.lift_π]
  congr 1

/-- The face map `δ i` of the Čech nerve is compatible with the structure maps. -/
lemma cechNerve_delta_comp_base (β : X ⟶ Y) (i : Fin 2) :
    (lcechNerve β).δ i ≫ Limits.WidePullback.base (fun _ : Fin 1 => β) =
      Limits.WidePullback.base (fun _ : Fin 2 => β) := by
  change Limits.WidePullback.lift (Limits.WidePullback.base (fun _ : Fin 2 => β))
      (fun j : Fin 1 => Limits.WidePullback.π (fun _ : Fin 2 => β)
        ((SimplexCategory.δ i).toOrderHom j)) (by simp)
    ≫ Limits.WidePullback.base (fun _ : Fin 1 => β) = _
  rw [Limits.WidePullback.lift_base]

/-- The first face map of the Čech nerve is the first projection of `X ×_Y X`. -/
lemma cechNerve_delta_zero (β : X ⟶ Y) :
    (lcechNerve β).δ (0 : Fin 2) = lcdelta0 β := by
  refine Limits.WidePullback.eq_lift_of_comp_eq (fun _ : Fin 1 => β) (lcbase2 β)
    (fun _ : Fin 1 => lcpi2 β 1) _ _ (fun j => ?_) (cechNerve_delta_comp_base β 0)
  have : j = (0 : Fin 1) := Subsingleton.elim j 0
  subst this
  exact cechNerve_delta_comp_pi1 β 0

/-- The second face map of the Čech nerve is the second projection of `X ×_Y X`. -/
lemma cechNerve_delta_one (β : X ⟶ Y) :
    (lcechNerve β).δ (1 : Fin 2) = lcdelta1 β := by
  refine Limits.WidePullback.eq_lift_of_comp_eq (fun _ : Fin 1 => β) (lcbase2 β)
    (fun _ : Fin 1 => lcpi2 β 0) _ _ (fun j => ?_) (cechNerve_delta_comp_base β 1)
  have : j = (0 : Fin 1) := Subsingleton.elim j 0
  subst this
  exact cechNerve_delta_comp_pi1 β 1

/-! ## §2. The level-`0` term is `X` -/

/-- The canonical identification of the level-`0` term of the Čech nerve with `X`. -/
noncomputable def lcechZeroIso (β : X ⟶ Y) : lcw1 β ≅ X where
  hom := lcpi1 β 0
  inv := Limits.WidePullback.lift β (fun _ : Fin 1 => 𝟙 X) (by intro j; simp)
  hom_inv_id := by
    apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
    · intro j
      rw [Category.assoc, Limits.WidePullback.lift_π]
      simp only [Category.comp_id, Category.id_comp]
      exact congrArg (fun k => lcpi1 β k) (Subsingleton.elim 0 j)
    · rw [Category.assoc, Limits.WidePullback.lift_base, Limits.WidePullback.π_arrow,
        Category.id_comp]
  inv_hom_id := Limits.WidePullback.lift_π _ _ _ _ _

lemma lcechZeroIso_hom_comp_beta (β : X ⟶ Y) :
    (lcechZeroIso β).hom ≫ β = lcbase1 β :=
  lcpi1_comp β

lemma lcechZeroIso_inv_comp_base (β : X ⟶ Y) :
    (lcechZeroIso β).inv ≫ lcbase1 β = β :=
  Limits.WidePullback.lift_base _ _ _ _

/-! ## §3. The cofork is a colimit -/

/-- An epimorphism of light condensed sets is an effective epimorphism: the category of sheaves of
types is a regular epi category. -/
lemma lbetaEffEpi (β : X ⟶ Y) (hβ : Epi β) : EffectiveEpi β := by
  letI := hβ
  exact (isRegularEpi_iff_effectiveEpi β).mp (IsRegularEpiCategory.regularEpiOfEpi β)

/-- The canonical `EffectiveEpiStruct` of `β`. -/
noncomputable def lbetaStruct (β : X ⟶ Y) (hβ : Epi β) : EffectiveEpiStruct β := by
  haveI := lbetaEffEpi β hβ
  exact EffectiveEpi.getStruct β

/-- The transposed "descent" map along the free/forget adjunction. -/
noncomputable def lcoforkE (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (lcdelta0 β)) ((free ℤ).map (lcdelta1 β))) :
    X ⟶ (LightCondensed.forget ℤ).obj s.pt :=
  (LightCondensed.freeForgetAdjunction ℤ).homEquiv X s.pt
    ((free ℤ).map (lcechZeroIso β).inv ≫ s.π)

/-- The transpose of the free-module image of any map coequalizing the two projections
descends along `β`. -/
lemma lcoforkE_spec (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (lcdelta0 β)) ((free ℤ).map (lcdelta1 β))) :
    ∀ {Z : LightCondSet} (g₁ g₂ : Z ⟶ X), g₁ ≫ β = g₂ ≫ β →
      g₁ ≫ lcoforkE β hβ s = g₂ ≫ lcoforkE β hβ s := by
  intro Z g₁ g₂ hg
  -- any pair coequalizing the structure maps factors through the wide pullback `X ×_Y X`
  have key : ∀ {Z : LightCondSet} (η₀ η₁ : Z ⟶ lcw1 β), η₀ ≫ lcbase1 β = η₁ ≫ lcbase1 β →
      (free ℤ).map η₀ ≫ s.π = (free ℤ).map η₁ ≫ s.π := by
    intro Z η₀ η₁ hη
    let fs : (j : Fin 2) → Z ⟶ X :=
      fun j => Fin.cases (η₁ ≫ lcpi1 β 0) (fun _ => η₀ ≫ lcpi1 β 0) j
    have hfs : ∀ j : Fin 2, fs j ≫ β = η₀ ≫ lcbase1 β := by
      intro j
      fin_cases j
      · show (η₁ ≫ lcpi1 β 0) ≫ β = η₀ ≫ lcbase1 β
        rw [Category.assoc, lcpi1_comp, hη]
      · show (η₀ ≫ lcpi1 β 0) ≫ β = η₀ ≫ lcbase1 β
        rw [Category.assoc, lcpi1_comp]
    let ζ : Z ⟶ lcw2 β := Limits.WidePullback.lift (η₀ ≫ lcbase1 β) fs hfs
    have hζ0 : ζ ≫ lcdelta0 β = η₀ := by
      apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
      · intro j
        have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
        subst hj
        rw [Category.assoc, lcdelta0_comp_pi1, Limits.WidePullback.lift_π]
        show fs 1 = η₀ ≫ lcpi1 β 0
        rfl
      · rw [Category.assoc, lcdelta0_comp_base, Limits.WidePullback.lift_base]
    have hζ1 : ζ ≫ lcdelta1 β = η₁ := by
      apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
      · intro j
        have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
        subst hj
        rw [Category.assoc, lcdelta1_comp_pi1, Limits.WidePullback.lift_π]
        show fs 0 = η₁ ≫ lcpi1 β 0
        rfl
      · rw [Category.assoc, lcdelta1_comp_base, Limits.WidePullback.lift_base]
        exact hη
    rw [← hζ0, ← hζ1, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      s.condition]
  have hv : (free ℤ).map g₁ ≫ ((free ℤ).map (lcechZeroIso β).inv ≫ s.π) =
      (free ℤ).map g₂ ≫ ((free ℤ).map (lcechZeroIso β).inv ≫ s.π) := by
    have h1 : g₁ ≫ (lcechZeroIso β).inv ≫ lcbase1 β = g₂ ≫ (lcechZeroIso β).inv ≫ lcbase1 β := by
      rw [lcechZeroIso_inv_comp_base, hg]
    rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    exact key _ _ h1
  calc g₁ ≫ lcoforkE β hβ s
      = (LightCondensed.freeForgetAdjunction ℤ).homEquiv Z s.pt
          ((free ℤ).map g₁ ≫ ((free ℤ).map (lcechZeroIso β).inv ≫ s.π)) :=
        (Adjunction.homEquiv_naturality_left (LightCondensed.freeForgetAdjunction ℤ) g₁ _).symm
    _ = (LightCondensed.freeForgetAdjunction ℤ).homEquiv Z s.pt
          ((free ℤ).map g₂ ≫ ((free ℤ).map (lcechZeroIso β).inv ≫ s.π)) := by rw [hv]
    _ = g₂ ≫ lcoforkE β hβ s :=
        (Adjunction.homEquiv_naturality_left (LightCondensed.freeForgetAdjunction ℤ) g₂ _)

/-- The descent map produced by the effective-epimorphism structure of `β`. -/
noncomputable def lcoforkDesc (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (lcdelta0 β)) ((free ℤ).map (lcdelta1 β))) :
    (free ℤ).obj Y ⟶ s.pt :=
  ((LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt).symm
    ((lbetaStruct β hβ).desc (lcoforkE β hβ s) (lcoforkE_spec β hβ s))

/-- Unfolding lemma for `lcoforkDesc`. -/
lemma lcoforkDesc_eq (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (lcdelta0 β)) ((free ℤ).map (lcdelta1 β))) :
    lcoforkDesc β hβ s =
      ((LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt).symm
        ((lbetaStruct β hβ).desc (lcoforkE β hβ s) (lcoforkE_spec β hβ s)) := rfl

/-- The factorisation property of the effective-epimorphism structure of `β`. -/
lemma lbetaStruct_fac (β : X ⟶ Y) (hβ : Epi β) {W : LightCondSet}
    (e : X ⟶ W)
    (h : ∀ {Z : LightCondSet} (g₁ g₂ : Z ⟶ X), g₁ ≫ β = g₂ ≫ β →
      g₁ ≫ e = g₂ ≫ e) :
    β ≫ (lbetaStruct β hβ).desc e h = e :=
  (lbetaStruct β hβ).fac e h

lemma lcoforkDesc_fac (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (lcdelta0 β)) ((free ℤ).map (lcdelta1 β))) :
    (free ℤ).map (lcbase1 β) ≫ lcoforkDesc β hβ s = s.π := by
  have h : (LightCondensed.freeForgetAdjunction ℤ).homEquiv (lcw1 β) s.pt
        ((free ℤ).map (lcbase1 β) ≫ lcoforkDesc β hβ s) =
      (LightCondensed.freeForgetAdjunction ℤ).homEquiv (lcw1 β) s.pt s.π := by
    rw [Adjunction.homEquiv_naturality_left, lcoforkDesc_eq, Equiv.apply_symm_apply,
      ← lcechZeroIso_hom_comp_beta β, Category.assoc, lbetaStruct_fac, lcoforkE,
      ← Adjunction.homEquiv_naturality_left, ← Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((LightCondensed.freeForgetAdjunction ℤ).homEquiv (lcw1 β) s.pt).injective h

lemma lcoforkDesc_uniq (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (lcdelta0 β)) ((free ℤ).map (lcdelta1 β)))
    (m : (free ℤ).obj Y ⟶ s.pt) (hm : (free ℤ).map (lcbase1 β) ≫ m = s.π) :
    m = lcoforkDesc β hβ s := by
  have hmem : (LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt m =
      (lbetaStruct β hβ).desc (lcoforkE β hβ s) (lcoforkE_spec β hβ s) := by
    apply (lbetaStruct β hβ).uniq
    rw [← Adjunction.homEquiv_naturality_left]
    congr 1
    have hmap : (free ℤ).map (lcechZeroIso β).inv ≫ (free ℤ).map (lcbase1 β) =
        (free ℤ).map β := by
      rw [← Functor.map_comp, lcechZeroIso_inv_comp_base]
    rw [← hmap, Category.assoc, hm]
  rw [lcoforkDesc_eq, ← hmem]
  exact (Equiv.symm_apply_apply _ m).symm

/-- **The Čech cofork is a colimit.**  For an epimorphism `β : X ⟶ Y` of light condensed sets,
the two face maps `ℤ[X ×_Y X] ⇉ ℤ[X]` and the augmentation have `ℤ[Y]` as their coequalizer. -/
noncomputable def cechCofork_isColimit (β : X ⟶ Y) (hβ : Epi β) :
    IsColimit (Cofork.ofπ (f := (free ℤ).map (lcdelta0 β)) (g := (free ℤ).map (lcdelta1 β))
      ((free ℤ).map (lcbase1 β)) (by
        rw [← Functor.map_comp, ← Functor.map_comp, lcdelta0_comp_base, lcdelta1_comp_base])) :=
  Cofork.IsColimit.mk _ (fun s => lcoforkDesc β hβ s)
    (fun s => lcoforkDesc_fac β hβ s) (fun s m hm => lcoforkDesc_uniq β hβ s m hm)

/-- The augmented simplicial object whose alternating-face complex is the Čech complex. -/
noncomputable abbrev cechAugObj (β : X ⟶ Y) : SimplicialObject.Augmented LightCondAb :=
  (SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
    (Arrow.augmentedCechNerve (Arrow.mk β))

theorem cech_descent_light_homologyMap_zero {X Y : LightCondSet.{0}} (β : X ⟶ Y) (hβ : Epi β) :
    IsIso (HomologicalComplex.homologyMap
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        ((SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
          (Arrow.augmentedCechNerve (Arrow.mk β)))) 0) := by
  let K : ChainComplex LightCondAb ℕ := AlternatingFaceMapComplex.obj (cechAugObj β).left
  let M : ChainComplex LightCondAb ℕ := (ChainComplex.single₀ LightCondAb).obj ((free ℤ).obj Y)
  let εc : K ⟶ M := AlternatingFaceMapComplex.ε.app (cechAugObj β)
  change IsIso (HomologicalComplex.homologyMap εc 0)
  -- the augmentation in degree `0` is the structure map of the level-`0` term
  have hε0 : εc.f 0 = (free ℤ).map (lcbase1 β) := by
    dsimp only [εc]
    rw [AlternatingFaceMapComplex.ε_app_f_zero]
    simp only [cechAugObj, SimplicialObject.Augmented.whiskeringObj]
    rfl
  -- the two face maps are the two projections of `X ×_Y X`
  have hδ0 : (cechAugObj β).left.δ (0 : Fin 2) = (free ℤ).map (lcdelta0 β) :=
    (show (cechAugObj β).left.δ (0 : Fin 2) =
        (free ℤ).map ((lcechNerve β).δ (0 : Fin 2)) from rfl).trans
      (congrArg (fun t => (free ℤ).map t) (cechNerve_delta_zero β))
  have hδ1 : (cechAugObj β).left.δ (1 : Fin 2) = (free ℤ).map (lcdelta1 β) :=
    (show (cechAugObj β).left.δ (1 : Fin 2) =
        (free ℤ).map ((lcechNerve β).δ (1 : Fin 2)) from rfl).trans
      (congrArg (fun t => (free ℤ).map t) (cechNerve_delta_one β))
  -- the augmentation coequalizes the two face maps
  have hhom : εc.f 0 = (cechAugObj β).hom.app (Opposite.op { len := 0 }) :=
    AlternatingFaceMapComplex.ε_app_f_zero (cechAugObj β)
  have hcond : (cechAugObj β).left.δ (0 : Fin 2) ≫ εc.f 0 =
      (cechAugObj β).left.δ (1 : Fin 2) ≫ εc.f 0 := by
    have step1 : (cechAugObj β).left.δ (0 : Fin 2) ≫ εc.f 0 =
        (cechAugObj β).left.δ (0 : Fin 2) ≫
          (cechAugObj β).hom.app (Opposite.op { len := 0 }) :=
      congrArg (fun t => (cechAugObj β).left.δ (0 : Fin 2) ≫ t) hhom
    have step2 : (cechAugObj β).left.δ (0 : Fin 2) ≫
          (cechAugObj β).hom.app (Opposite.op { len := 0 }) =
        (cechAugObj β).hom.app (Opposite.op { len := 1 }) :=
      (SimplicialObject.δ_naturality (f := (cechAugObj β).hom) (n := 0)
        (0 : Fin 2)).trans (Category.comp_id _)
    have step3 : (cechAugObj β).hom.app (Opposite.op { len := 1 }) =
        (cechAugObj β).left.δ (1 : Fin 2) ≫
          (cechAugObj β).hom.app (Opposite.op { len := 0 }) :=
      ((SimplicialObject.δ_naturality (f := (cechAugObj β).hom) (n := 0)
        (1 : Fin 2)).trans (Category.comp_id _)).symm
    have step4 : (cechAugObj β).left.δ (1 : Fin 2) ≫
          (cechAugObj β).hom.app (Opposite.op { len := 0 }) =
        (cechAugObj β).left.δ (1 : Fin 2) ≫ εc.f 0 :=
      (congrArg (fun t => (cechAugObj β).left.δ (1 : Fin 2) ≫ t) hhom).symm
    exact step1.trans (step2.trans (step3.trans step4))
  -- the cofork of the two face maps is a colimit
  have hc : IsColimit (Cofork.ofπ (f := (cechAugObj β).left.δ (0 : Fin 2))
      (g := (cechAugObj β).left.δ (1 : Fin 2)) (εc.f 0) hcond) :=
    Work.ANALYTIC.CechPt.cofork_isColimit_transport hδ0.symm hδ1.symm hε0.symm
      (cechCofork_isColimit β hβ)
  -- `K.d 1 0` is the difference of the two face maps, so its cokernel projection coequalizes them
  have hKd : K.d 1 0 = (cechAugObj β).left.δ (0 : Fin 2) - (cechAugObj β).left.δ (1 : Fin 2) := by
    have h : K.d 1 0 = ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (cechAugObj β).left.δ i := by
      rw [AlternatingFaceMapComplex.obj_d_eq]
    rw [h, Fin.sum_univ_two, sub_eq_add_neg]
    simp
  have hpO_cond : (cechAugObj β).left.δ (0 : Fin 2) ≫ K.pOpcycles 0 =
      (cechAugObj β).left.δ (1 : Fin 2) ≫ K.pOpcycles 0 := by
    have h0 : K.d 1 0 ≫ K.pOpcycles 0 = 0 := K.d_pOpcycles 1 0
    rw [hKd, Preadditive.sub_comp] at h0
    exact sub_eq_zero.mp h0
  -- the isomorphism `M.X 0 ≅ ℤ[Y]`
  let x := HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 ((free ℤ).obj Y)
  -- the augmentation, postcomposed with that isomorphism, is a map `K.X 0 ⟶ ℤ[Y]`
  let π' : K.X 0 ⟶ (free ℤ).obj Y := εc.f 0 ≫ x.hom
  have hkill : K.d 1 0 ≫ εc.f 0 = 0 := by
    rw [← HomologicalComplex.Hom.comm εc 1 0]
    have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      ((free ℤ).obj Y) 1 (by decide)
    have h1 : εc.f 1 = 0 := hz.eq_of_tgt _ _
    rw [h1, zero_comp]
  have hkill' : K.d 1 0 ≫ π' = 0 := by
    dsimp only [π']
    rw [← Category.assoc, hkill, zero_comp]
  have hcondπ : (cechAugObj β).left.δ (0 : Fin 2) ≫ π' =
      (cechAugObj β).left.δ (1 : Fin 2) ≫ π' := by
    dsimp only [π']
    rw [← Category.assoc, ← Category.assoc, hcond]
  -- the Čech cofork with the twisted structure map is a colimit as well
  have hcπ : IsColimit (Cofork.ofπ (f := (cechAugObj β).left.δ (0 : Fin 2))
      (g := (cechAugObj β).left.δ (1 : Fin 2)) π' hcondπ) :=
    Work.ANALYTIC.CechPt.cofork_isColimit_comp_iso x hc
  -- the two maps exhibiting `ℤ[Y]` as the cokernel of `K.d 1 0`
  let w : (free ℤ).obj Y ⟶ K.opcycles 0 := Cofork.IsColimit.desc hcπ (K.pOpcycles 0) hpO_cond
  have hw : π' ≫ w = K.pOpcycles 0 := Cofork.IsColimit.π_desc' hcπ _ _
  let w' : K.opcycles 0 ⟶ (free ℤ).obj Y :=
    K.descOpcycles π' 1 (ComplexShape.prev_eq' (ComplexShape.down ℕ) rfl) hkill'
  have hw' : K.pOpcycles 0 ≫ w' = π' := K.p_descOpcycles _ _ _ _
  -- they are mutually inverse
  have hw'w : w' ≫ w = 𝟙 (K.opcycles 0) := by
    rw [← cancel_epi (K.pOpcycles 0), ← Category.assoc, hw', hw, Category.comp_id]
  have hww' : w ≫ w' = 𝟙 ((free ℤ).obj Y) := by
    apply Cofork.IsColimit.hom_ext hcπ
    rw [Cofork.π_ofπ, ← Category.assoc, hw, hw']
    exact (Category.comp_id _).symm
  haveI hw'is : IsIso w' := IsIso.mk ⟨w, hw'w, hww'⟩
  -- comparison with the homology of the single-object complex
  let S := HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 ((free ℤ).obj Y)
  let S' := HomologicalComplex.singleObjOpcyclesSelfIso (ComplexShape.down ℕ) 0 ((free ℤ).obj Y)
  have hopc : HomologicalComplex.opcyclesMap εc 0 ≫ S'.inv = w' := by
    rw [← cancel_epi (K.pOpcycles 0), ← Category.assoc, HomologicalComplex.p_opcyclesMap,
      Category.assoc, HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv]
    exact hw'.symm
  have hrel : HomologicalComplex.homologyMap εc 0 ≫ S.hom =
      K.homologyι 0 ≫ (HomologicalComplex.opcyclesMap εc 0 ≫ S'.inv) := by
    have h := congrArg (fun t : K.homology 0 ⟶ M.opcycles 0 => t ≫ S'.inv)
      (HomologicalComplex.homologyι_naturality (φ := εc) 0)
    rw [Category.assoc, HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv] at h
    exact h
  have hcomp : IsIso (K.homologyι 0 ≫ (HomologicalComplex.opcyclesMap εc 0 ≫ S'.inv)) := by
    rw [hopc]
    exact IsIso.comp_isIso' (by infer_instance : IsIso (K.homologyι 0)) hw'is
  haveI hfinal : IsIso (HomologicalComplex.homologyMap εc 0 ≫ S.hom) := by
    rw [hrel]
    exact hcomp
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap εc 0) S.hom

end

end Work.ANALYTIC.CechLight
