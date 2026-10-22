import Mathlib
import Submission.Work.ANALYTIC.CechPt.Defs
import Submission.Work.ANALYTIC.CechPt.Nerve

/-!
# `H₀` of the Čech complex of a cover is `ℤ[Y]`

For `β : X ⟶ Y` an epimorphism of light condensed sets with `X` light profinite, we prove that
the degree-`0` homology of the alternating-face-map complex of the free-module Čech nerve
`p ↦ ℤ[X ×_Y ⋯ ×_Y X]` is `ℤ[Y]` via the augmentation.  Equivalently, the cofork

  `ℤ[X ×_Y X] ⇉ ℤ[X] ⟶ ℤ[Y]`

given by the two face maps `δ₀, δ₁` and the augmentation is a colimit.

The argument has two parts.

* The bottom of the Čech nerve of `β` is the wide pullback `X ×_Y X` (of two copies of `X`),
  and the two face maps `δ₀, δ₁ : X ×_Y X ⟶ X` are the two projections.  The augmentation
  `β : X ⟶ Y` coequalizes them.
* Since `Epi` morphisms in `LightCondSet` are regular (the category of sheaves of types is a
  regular epi category), `β` is an *effective* epimorphism: any map out of `X` coequalizing the
  projections of the kernel pair descends to `Y`.  Applying the free-module functor `ℤ[-]`
  (a left adjoint) and transposing along the free/forget adjunction turns this into the
  statement that `ℤ[Y]` is the coequalizer of the two face maps.
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed AlgebraicTopology

noncomputable section

variable {X : LightProfinite.{0}} {Y : LightCondSet.{0}}

/-! ## §1. The bottom of the Čech nerve -/

/-- The level-`0` term of the Čech nerve of `β`, i.e. the wide pullback of one copy of `X`
over `Y`. -/
noncomputable abbrev cw1 (β : LightProfinite.toCondensed X ⟶ Y) : LightCondSet :=
  Limits.widePullback Y (fun _ : Fin 1 => X.toCondensed) (fun _ => β)

/-- The level-`1` term of the Čech nerve of `β`, i.e. the wide pullback of two copies of `X`
over `Y` (`X ×_Y X`). -/
noncomputable abbrev cw2 (β : LightProfinite.toCondensed X ⟶ Y) : LightCondSet :=
  Limits.widePullback Y (fun _ : Fin 2 => X.toCondensed) (fun _ => β)

/-- The `j`-th projection of the level-`0` term. -/
noncomputable abbrev cpi1 (β : LightProfinite.toCondensed X ⟶ Y) (j : Fin 1) :
    cw1 β ⟶ X.toCondensed :=
  Limits.WidePullback.π (fun _ : Fin 1 => β) j

/-- The structure map of the level-`0` term. -/
noncomputable abbrev cbase1 (β : LightProfinite.toCondensed X ⟶ Y) : cw1 β ⟶ Y :=
  Limits.WidePullback.base (fun _ : Fin 1 => β)

/-- The `j`-th projection of the level-`1` term. -/
noncomputable abbrev cpi2 (β : LightProfinite.toCondensed X ⟶ Y) (j : Fin 2) :
    cw2 β ⟶ X.toCondensed :=
  Limits.WidePullback.π (fun _ : Fin 2 => β) j

/-- The structure map of the level-`1` term. -/
noncomputable abbrev cbase2 (β : LightProfinite.toCondensed X ⟶ Y) : cw2 β ⟶ Y :=
  Limits.WidePullback.base (fun _ : Fin 2 => β)

lemma cpi1_comp (β : LightProfinite.toCondensed X ⟶ Y) :
    cpi1 β 0 ≫ β = cbase1 β :=
  Limits.WidePullback.π_arrow _ _

lemma cpi2_comp (β : LightProfinite.toCondensed X ⟶ Y) (j : Fin 2) :
    cpi2 β j ≫ β = cbase2 β :=
  Limits.WidePullback.π_arrow _ _

/-- The face map `δ₀` at the bottom of the Čech nerve, as a map `X ×_Y X ⟶ X`. -/
noncomputable abbrev cdelta0 (β : LightProfinite.toCondensed X ⟶ Y) : cw2 β ⟶ cw1 β :=
  Limits.WidePullback.lift (cbase2 β) (fun _ : Fin 1 => cpi2 β 1)
    (by intro j; exact cpi2_comp β 1)

/-- The face map `δ₁` at the bottom of the Čech nerve, as a map `X ×_Y X ⟶ X`. -/
noncomputable abbrev cdelta1 (β : LightProfinite.toCondensed X ⟶ Y) : cw2 β ⟶ cw1 β :=
  Limits.WidePullback.lift (cbase2 β) (fun _ : Fin 1 => cpi2 β 0)
    (by intro j; exact cpi2_comp β 0)

lemma cdelta0_comp_pi1 (β : LightProfinite.toCondensed X ⟶ Y) :
    cdelta0 β ≫ cpi1 β 0 = cpi2 β 1 :=
  Limits.WidePullback.lift_π _ _ _ _ _

lemma cdelta1_comp_pi1 (β : LightProfinite.toCondensed X ⟶ Y) :
    cdelta1 β ≫ cpi1 β 0 = cpi2 β 0 :=
  Limits.WidePullback.lift_π _ _ _ _ _

lemma cdelta0_comp_base (β : LightProfinite.toCondensed X ⟶ Y) :
    cdelta0 β ≫ cbase1 β = cbase2 β :=
  Limits.WidePullback.lift_base _ _ _ _

lemma cdelta1_comp_base (β : LightProfinite.toCondensed X ⟶ Y) :
    cdelta1 β ≫ cbase1 β = cbase2 β :=
  Limits.WidePullback.lift_base _ _ _ _

/-- The face map `δ i` of the Čech nerve, composed with the identification of the level-`0` term
with `X`, is the `i`-th projection of the wide pullback `X ×_Y X`. -/
lemma cechNerve_delta_comp_pi1 (β : LightProfinite.toCondensed X ⟶ Y) (i : Fin 2) :
    (cechNerve β).δ i ≫ Limits.WidePullback.π (fun _ : Fin 1 => β) (0 : Fin 1) =
      Limits.WidePullback.π (fun _ : Fin 2 => β) (Fin.succAbove i 0) := by
  change Limits.WidePullback.lift (Limits.WidePullback.base (fun _ : Fin 2 => β))
      (fun j : Fin 1 => Limits.WidePullback.π (fun _ : Fin 2 => β)
        ((SimplexCategory.δ i).toOrderHom j)) (by simp)
    ≫ Limits.WidePullback.π (fun _ : Fin 1 => β) 0 = _
  rw [Limits.WidePullback.lift_π]
  congr 1

/-- The face map `δ i` of the Čech nerve is compatible with the structure maps. -/
lemma cechNerve_delta_comp_base (β : LightProfinite.toCondensed X ⟶ Y) (i : Fin 2) :
    (cechNerve β).δ i ≫ Limits.WidePullback.base (fun _ : Fin 1 => β) =
      Limits.WidePullback.base (fun _ : Fin 2 => β) := by
  change Limits.WidePullback.lift (Limits.WidePullback.base (fun _ : Fin 2 => β))
      (fun j : Fin 1 => Limits.WidePullback.π (fun _ : Fin 2 => β)
        ((SimplexCategory.δ i).toOrderHom j)) (by simp)
    ≫ Limits.WidePullback.base (fun _ : Fin 1 => β) = _
  rw [Limits.WidePullback.lift_base]

/-- The first face map of the Čech nerve is the first projection of `X ×_Y X`. -/
lemma cechNerve_delta_zero (β : LightProfinite.toCondensed X ⟶ Y) :
    (cechNerve β).δ (0 : Fin 2) = cdelta0 β := by
  refine Limits.WidePullback.eq_lift_of_comp_eq (fun _ : Fin 1 => β) (cbase2 β)
    (fun _ : Fin 1 => cpi2 β 1) _ _ (fun j => ?_) (cechNerve_delta_comp_base β 0)
  have : j = (0 : Fin 1) := Subsingleton.elim j 0
  subst this
  exact cechNerve_delta_comp_pi1 β 0

/-- The second face map of the Čech nerve is the second projection of `X ×_Y X`. -/
lemma cechNerve_delta_one (β : LightProfinite.toCondensed X ⟶ Y) :
    (cechNerve β).δ (1 : Fin 2) = cdelta1 β := by
  refine Limits.WidePullback.eq_lift_of_comp_eq (fun _ : Fin 1 => β) (cbase2 β)
    (fun _ : Fin 1 => cpi2 β 0) _ _ (fun j => ?_) (cechNerve_delta_comp_base β 1)
  have : j = (0 : Fin 1) := Subsingleton.elim j 0
  subst this
  exact cechNerve_delta_comp_pi1 β 1

/-! ## §2. The level-`0` term is `X` -/

/-- The canonical identification of the level-`0` term of the Čech nerve with `X`. -/
noncomputable def cechZeroIso (β : LightProfinite.toCondensed X ⟶ Y) :
    cw1 β ≅ X.toCondensed where
  hom := cpi1 β 0
  inv := Limits.WidePullback.lift β (fun _ : Fin 1 => 𝟙 X.toCondensed) (by intro j; simp)
  hom_inv_id := by
    apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
    · intro j
      rw [Category.assoc, Limits.WidePullback.lift_π]
      simp only [Category.comp_id, Category.id_comp]
      exact congrArg (fun k => cpi1 β k) (Subsingleton.elim 0 j)
    · rw [Category.assoc, Limits.WidePullback.lift_base, Limits.WidePullback.π_arrow,
        Category.id_comp]
  inv_hom_id := Limits.WidePullback.lift_π _ _ _ _ _

lemma cechZeroIso_hom_comp_beta (β : LightProfinite.toCondensed X ⟶ Y) :
    (cechZeroIso β).hom ≫ β = cbase1 β :=
  cpi1_comp β

lemma cechZeroIso_inv_comp_base (β : LightProfinite.toCondensed X ⟶ Y) :
    (cechZeroIso β).inv ≫ cbase1 β = β :=
  Limits.WidePullback.lift_base _ _ _ _

/-! ## §3. The cofork is a colimit -/

/-- An epimorphism of light condensed sets is an effective epimorphism: the category of sheaves of
types is a regular epi category. -/
lemma betaEffEpi (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β) :
    EffectiveEpi β := by
  letI := hβ
  exact (isRegularEpi_iff_effectiveEpi β).mp (IsRegularEpiCategory.regularEpiOfEpi β)

/-- The canonical `EffectiveEpiStruct` of `β`. -/
noncomputable def betaStruct (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β) :
    EffectiveEpiStruct β := by
  haveI := betaEffEpi β hβ
  exact EffectiveEpi.getStruct β

/-- The transposed "descent" map along the free/forget adjunction. -/
noncomputable def coforkE (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cdelta0 β)) ((free ℤ).map (cdelta1 β))) :
    X.toCondensed ⟶ (LightCondensed.forget ℤ).obj s.pt :=
  (LightCondensed.freeForgetAdjunction ℤ).homEquiv X.toCondensed s.pt
    ((free ℤ).map (cechZeroIso β).inv ≫ s.π)

/-- The transpose of the free-module image of any map coequalizing the two projections
descends along `β`. -/
lemma coforkE_spec (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cdelta0 β)) ((free ℤ).map (cdelta1 β))) :
    ∀ {Z : LightCondSet} (g₁ g₂ : Z ⟶ X.toCondensed), g₁ ≫ β = g₂ ≫ β →
      g₁ ≫ coforkE β hβ s = g₂ ≫ coforkE β hβ s := by
  intro Z g₁ g₂ hg
  -- any pair coequalizing the structure maps factors through the wide pullback `X ×_Y X`
  have key : ∀ {Z : LightCondSet} (η₀ η₁ : Z ⟶ cw1 β), η₀ ≫ cbase1 β = η₁ ≫ cbase1 β →
      (free ℤ).map η₀ ≫ s.π = (free ℤ).map η₁ ≫ s.π := by
    intro Z η₀ η₁ hη
    let fs : (j : Fin 2) → Z ⟶ X.toCondensed :=
      fun j => Fin.cases (η₁ ≫ cpi1 β 0) (fun _ => η₀ ≫ cpi1 β 0) j
    have hfs : ∀ j : Fin 2, fs j ≫ β = η₀ ≫ cbase1 β := by
      intro j
      fin_cases j
      · show (η₁ ≫ cpi1 β 0) ≫ β = η₀ ≫ cbase1 β
        rw [Category.assoc, cpi1_comp, hη]
      · show (η₀ ≫ cpi1 β 0) ≫ β = η₀ ≫ cbase1 β
        rw [Category.assoc, cpi1_comp]
    let ζ : Z ⟶ cw2 β := Limits.WidePullback.lift (η₀ ≫ cbase1 β) fs hfs
    have hζ0 : ζ ≫ cdelta0 β = η₀ := by
      apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
      · intro j
        have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
        subst hj
        rw [Category.assoc, cdelta0_comp_pi1, Limits.WidePullback.lift_π]
        show fs 1 = η₀ ≫ cpi1 β 0
        rfl
      · rw [Category.assoc, cdelta0_comp_base, Limits.WidePullback.lift_base]
    have hζ1 : ζ ≫ cdelta1 β = η₁ := by
      apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
      · intro j
        have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
        subst hj
        rw [Category.assoc, cdelta1_comp_pi1, Limits.WidePullback.lift_π]
        show fs 0 = η₁ ≫ cpi1 β 0
        rfl
      · rw [Category.assoc, cdelta1_comp_base, Limits.WidePullback.lift_base]
        exact hη
    rw [← hζ0, ← hζ1, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      s.condition]
  have hv : (free ℤ).map g₁ ≫ ((free ℤ).map (cechZeroIso β).inv ≫ s.π) =
      (free ℤ).map g₂ ≫ ((free ℤ).map (cechZeroIso β).inv ≫ s.π) := by
    have h1 : g₁ ≫ (cechZeroIso β).inv ≫ cbase1 β = g₂ ≫ (cechZeroIso β).inv ≫ cbase1 β := by
      rw [cechZeroIso_inv_comp_base, hg]
    rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    exact key _ _ h1
  calc g₁ ≫ coforkE β hβ s
      = (LightCondensed.freeForgetAdjunction ℤ).homEquiv Z s.pt
          ((free ℤ).map g₁ ≫ ((free ℤ).map (cechZeroIso β).inv ≫ s.π)) :=
        (Adjunction.homEquiv_naturality_left (LightCondensed.freeForgetAdjunction ℤ) g₁ _).symm
    _ = (LightCondensed.freeForgetAdjunction ℤ).homEquiv Z s.pt
          ((free ℤ).map g₂ ≫ ((free ℤ).map (cechZeroIso β).inv ≫ s.π)) := by rw [hv]
    _ = g₂ ≫ coforkE β hβ s :=
        (Adjunction.homEquiv_naturality_left (LightCondensed.freeForgetAdjunction ℤ) g₂ _)

/-- The descent map produced by the effective-epimorphism structure of `β`. -/
noncomputable def coforkDesc (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cdelta0 β)) ((free ℤ).map (cdelta1 β))) :
    (free ℤ).obj Y ⟶ s.pt :=
  ((LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt).symm
    ((betaStruct β hβ).desc (coforkE β hβ s) (coforkE_spec β hβ s))

/-- Unfolding lemma for `coforkDesc`. -/
lemma coforkDesc_eq (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cdelta0 β)) ((free ℤ).map (cdelta1 β))) :
    coforkDesc β hβ s =
      ((LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt).symm
        ((betaStruct β hβ).desc (coforkE β hβ s) (coforkE_spec β hβ s)) := rfl

/-- The factorisation property of the effective-epimorphism structure of `β`. -/
lemma betaStruct_fac (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β) {W : LightCondSet}
    (e : X.toCondensed ⟶ W)
    (h : ∀ {Z : LightCondSet} (g₁ g₂ : Z ⟶ X.toCondensed), g₁ ≫ β = g₂ ≫ β →
      g₁ ≫ e = g₂ ≫ e) :
    β ≫ (betaStruct β hβ).desc e h = e :=
  (betaStruct β hβ).fac e h

lemma coforkDesc_fac (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cdelta0 β)) ((free ℤ).map (cdelta1 β))) :
    (free ℤ).map (cbase1 β) ≫ coforkDesc β hβ s = s.π := by
  have h : (LightCondensed.freeForgetAdjunction ℤ).homEquiv (cw1 β) s.pt
        ((free ℤ).map (cbase1 β) ≫ coforkDesc β hβ s) =
      (LightCondensed.freeForgetAdjunction ℤ).homEquiv (cw1 β) s.pt s.π := by
    rw [Adjunction.homEquiv_naturality_left, coforkDesc_eq, Equiv.apply_symm_apply,
      ← cechZeroIso_hom_comp_beta β, Category.assoc, betaStruct_fac, coforkE,
      ← Adjunction.homEquiv_naturality_left, ← Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((LightCondensed.freeForgetAdjunction ℤ).homEquiv (cw1 β) s.pt).injective h

lemma coforkDesc_uniq (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cdelta0 β)) ((free ℤ).map (cdelta1 β)))
    (m : (free ℤ).obj Y ⟶ s.pt) (hm : (free ℤ).map (cbase1 β) ≫ m = s.π) :
    m = coforkDesc β hβ s := by
  have hmem : (LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt m =
      (betaStruct β hβ).desc (coforkE β hβ s) (coforkE_spec β hβ s) := by
    apply (betaStruct β hβ).uniq
    rw [← Adjunction.homEquiv_naturality_left]
    congr 1
    have hmap : (free ℤ).map (cechZeroIso β).inv ≫ (free ℤ).map (cbase1 β) =
        (free ℤ).map β := by
      rw [← Functor.map_comp, cechZeroIso_inv_comp_base]
    rw [← hmap, Category.assoc, hm]
  rw [coforkDesc_eq, ← hmem]
  exact (Equiv.symm_apply_apply _ m).symm

/-- **The Čech cofork is a colimit.**  For an epimorphism `β : X ⟶ Y` of light condensed sets
with `X` light profinite, the two face maps `ℤ[X ×_Y X] ⇉ ℤ[X]` and the augmentation have
`ℤ[Y]` as their coequalizer. -/
noncomputable def cechCofork_isColimit (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β) :
    IsColimit (Cofork.ofπ (f := (free ℤ).map (cdelta0 β)) (g := (free ℤ).map (cdelta1 β))
      ((free ℤ).map (cbase1 β)) (by
        rw [← Functor.map_comp, ← Functor.map_comp, cdelta0_comp_base, cdelta1_comp_base])) :=
  Cofork.IsColimit.mk _ (fun s => coforkDesc β hβ s)
    (fun s => coforkDesc_fac β hβ s) (fun s m hm => coforkDesc_uniq β hβ s m hm)

/-- The augmented simplicial object whose alternating-face complex is the Čech complex. -/
noncomputable abbrev cechAugObj (β : LightProfinite.toCondensed X ⟶ Y) :
    SimplicialObject.Augmented LightCondAb :=
  (SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
    (Arrow.augmentedCechNerve (Arrow.mk β))

/-- Transport of the colimit property of a cofork along equalities of its two legs and of its
structure map. -/
noncomputable def cofork_isColimit_transport {C : Type*} [Category C] {X Y P : C}
    {f g f' g' : X ⟶ Y} {π : Y ⟶ P} {π' : Y ⟶ P} (hf : f = f') (hg : g = g') (hπ : π = π')
    {hc : f ≫ π = g ≫ π} {hc' : f' ≫ π' = g' ≫ π'}
    (h : IsColimit (Cofork.ofπ (f := f) (g := g) π hc)) :
    IsColimit (Cofork.ofπ (f := f') (g := g') π' hc') := by
  subst hf
  subst hg
  subst hπ
  exact h

/-- Postcomposing the structure map of a colimit cofork with an isomorphism gives again a colimit
cofork. -/
noncomputable def cofork_isColimit_comp_iso {C : Type*} [Category C] {X Y P P' : C} {f g : X ⟶ Y}
    {π : Y ⟶ P} (e : P ≅ P') {hc : f ≫ π = g ≫ π}
    (h : IsColimit (Cofork.ofπ (f := f) (g := g) π hc)) :
    IsColimit (Cofork.ofπ (f := f) (g := g) (π ≫ e.hom)
      (by rw [← Category.assoc, ← Category.assoc, hc])) := by
  refine Cofork.IsColimit.mk _ (fun s => e.inv ≫ Cofork.IsColimit.desc h s.π s.condition) ?_ ?_
  · intro s
    rw [Cofork.π_ofπ, Category.assoc, Iso.hom_inv_id_assoc]
    exact Cofork.IsColimit.π_desc' h s.π s.condition
  · intro s m hm
    have hm'' : (π ≫ e.hom) ≫ m = s.π := by
      rw [Cofork.π_ofπ] at hm
      exact hm
    have hdesc : π ≫ Cofork.IsColimit.desc h s.π s.condition = s.π :=
      Cofork.IsColimit.π_desc' h s.π s.condition
    have hm' : e.hom ≫ m = Cofork.IsColimit.desc h s.π s.condition := by
      apply Cofork.IsColimit.hom_ext h
      rw [Cofork.π_ofπ, ← Category.assoc, hm'', hdesc]
    exact (Iso.inv_hom_id_assoc e m).symm.trans (congrArg (fun t => e.inv ≫ t) hm')

end

theorem cech_h0 {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β) :
    IsIso (HomologicalComplex.homologyMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
        (Arrow.augmentedCechNerve (Arrow.mk β)))) 0) := by
  let K : ChainComplex LightCondAb ℕ := AlternatingFaceMapComplex.obj (cechAugObj β).left
  let M : ChainComplex LightCondAb ℕ := (ChainComplex.single₀ LightCondAb).obj ((free ℤ).obj Y)
  let εc : K ⟶ M := AlternatingFaceMapComplex.ε.app (cechAugObj β)
  change IsIso (HomologicalComplex.homologyMap εc 0)
  -- the augmentation in degree `0` is the structure map of the level-`0` term
  have hε0 : εc.f 0 = (free ℤ).map (cbase1 β) := by
    dsimp only [εc]
    rw [AlternatingFaceMapComplex.ε_app_f_zero]
    simp only [cechAugObj, SimplicialObject.Augmented.whiskeringObj]
    rfl
  -- the two face maps are the two projections of `X ×_Y X`
  have hδ0 : (cechAugObj β).left.δ (0 : Fin 2) = (free ℤ).map (cdelta0 β) :=
    (show (cechAugObj β).left.δ (0 : Fin 2) =
        (free ℤ).map ((cechNerve β).δ (0 : Fin 2)) from rfl).trans
      (congrArg (fun t => (free ℤ).map t) (cechNerve_delta_zero β))
  have hδ1 : (cechAugObj β).left.δ (1 : Fin 2) = (free ℤ).map (cdelta1 β) :=
    (show (cechAugObj β).left.δ (1 : Fin 2) =
        (free ℤ).map ((cechNerve β).δ (1 : Fin 2)) from rfl).trans
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
    cofork_isColimit_transport hδ0.symm hδ1.symm hε0.symm (cechCofork_isColimit β hβ)
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
    cofork_isColimit_comp_iso x hc
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

end Work.ANALYTIC.CechPt
