import Mathlib

/-!
# Čech `H⁰` for an arbitrary light condensed source

For `β : X ⟶ Y` an epimorphism of light condensed sets, with `X` an *arbitrary* light condensed
set (not necessarily light profinite), the degree-`0` homology of the augmentation `ε` of the
free-module Čech complex of `β` is an isomorphism.  Equivalently, the cofork

  `ℤ[X ×_Y X] ⇉ ℤ[X] ⟶ ℤ[Y]`

given by the two face maps `δ₀, δ₁` and the augmentation is a colimit.

The argument is the one of `Submission/Work/ANALYTIC/CechPt/cech_h0.lean`, which proves the
light-profinite case; it never uses profiniteness of the source beyond the binder type of `β`:

* the bottom of the Čech nerve of `β` is the wide pullback `X ×_Y X` of two copies of `X`, with
  face maps the two projections, and the augmentation `β : X ⟶ Y` coequalizes them
  (`cgdelta0`, `cgdelta1`, `cgbase1`);
* an epimorphism of light condensed sets is a *regular* epimorphism (sheaves of types form a
  regular epi category), hence an *effective* epimorphism: any map out of `X` coequalizing the two
  projections descends to `Y` (`cgEffEpi`, `cgStruct`);
* transposing along the free/forget adjunction turns this into the statement that `ℤ[Y]` is the
  coequalizer of the two face maps (`cgCofork_isColimit`);
* comparing that colimit with the cokernel of the differential `K.d 1 0 = δ₀ - δ₁` of the
  alternating face map complex identifies `H₀` of the augmentation with the identity of `ℤ[Y]`.

Everything below is self-contained (the file imports only `Mathlib`).
-/

namespace Work.ANALYTIC.CechGen

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

open _root_.LightCondensed
open AlgebraicTopology

noncomputable section

variable {X : LightCondSet.{0}} {Y : LightCondSet.{0}}

/-! ## §1. The bottom of the Čech nerve -/

/-- The Čech nerve of a map of light condensed sets, as a simplicial object. -/
noncomputable abbrev cgNerve (β : X ⟶ Y) : SimplicialObject LightCondSet.{0} :=
  Arrow.cechNerve (Arrow.mk β)

/-- The level-`0` term of the Čech nerve of `β`, i.e. the wide pullback of one copy of `X`
over `Y`. -/
noncomputable abbrev cgw1 (β : X ⟶ Y) : LightCondSet :=
  Limits.widePullback Y (fun _ : Fin 1 => X) (fun _ => β)

/-- The level-`1` term of the Čech nerve of `β`, i.e. the wide pullback of two copies of `X`
over `Y` (`X ×_Y X`). -/
noncomputable abbrev cgw2 (β : X ⟶ Y) : LightCondSet :=
  Limits.widePullback Y (fun _ : Fin 2 => X) (fun _ => β)

/-- The `j`-th projection of the level-`0` term. -/
noncomputable abbrev cgpi1 (β : X ⟶ Y) (j : Fin 1) : cgw1 β ⟶ X :=
  Limits.WidePullback.π (fun _ : Fin 1 => β) j

/-- The structure map of the level-`0` term. -/
noncomputable abbrev cgbase1 (β : X ⟶ Y) : cgw1 β ⟶ Y :=
  Limits.WidePullback.base (fun _ : Fin 1 => β)

/-- The `j`-th projection of the level-`1` term. -/
noncomputable abbrev cgpi2 (β : X ⟶ Y) (j : Fin 2) : cgw2 β ⟶ X :=
  Limits.WidePullback.π (fun _ : Fin 2 => β) j

/-- The structure map of the level-`1` term. -/
noncomputable abbrev cgbase2 (β : X ⟶ Y) : cgw2 β ⟶ Y :=
  Limits.WidePullback.base (fun _ : Fin 2 => β)

lemma cgpi1_comp (β : X ⟶ Y) : cgpi1 β 0 ≫ β = cgbase1 β :=
  Limits.WidePullback.π_arrow _ _

lemma cgpi2_comp (β : X ⟶ Y) (j : Fin 2) : cgpi2 β j ≫ β = cgbase2 β :=
  Limits.WidePullback.π_arrow _ _

/-- The face map `δ₀` at the bottom of the Čech nerve, as a map `X ×_Y X ⟶ X`. -/
noncomputable abbrev cgdelta0 (β : X ⟶ Y) : cgw2 β ⟶ cgw1 β :=
  Limits.WidePullback.lift (cgbase2 β) (fun _ : Fin 1 => cgpi2 β 1)
    (by intro j; exact cgpi2_comp β 1)

/-- The face map `δ₁` at the bottom of the Čech nerve, as a map `X ×_Y X ⟶ X`. -/
noncomputable abbrev cgdelta1 (β : X ⟶ Y) : cgw2 β ⟶ cgw1 β :=
  Limits.WidePullback.lift (cgbase2 β) (fun _ : Fin 1 => cgpi2 β 0)
    (by intro j; exact cgpi2_comp β 0)

lemma cgdelta0_comp_pi1 (β : X ⟶ Y) : cgdelta0 β ≫ cgpi1 β 0 = cgpi2 β 1 :=
  Limits.WidePullback.lift_π _ _ _ _ _

lemma cgdelta1_comp_pi1 (β : X ⟶ Y) : cgdelta1 β ≫ cgpi1 β 0 = cgpi2 β 0 :=
  Limits.WidePullback.lift_π _ _ _ _ _

lemma cgdelta0_comp_base (β : X ⟶ Y) : cgdelta0 β ≫ cgbase1 β = cgbase2 β :=
  Limits.WidePullback.lift_base _ _ _ _

lemma cgdelta1_comp_base (β : X ⟶ Y) : cgdelta1 β ≫ cgbase1 β = cgbase2 β :=
  Limits.WidePullback.lift_base _ _ _ _

/-- The face map `δ i` of the Čech nerve, composed with the identification of the level-`0` term
with `X`, is the `i`-th projection of the wide pullback `X ×_Y X`. -/
lemma cgNerve_delta_comp_pi1 (β : X ⟶ Y) (i : Fin 2) :
    (cgNerve β).δ i ≫ Limits.WidePullback.π (fun _ : Fin 1 => β) (0 : Fin 1) =
      Limits.WidePullback.π (fun _ : Fin 2 => β) (Fin.succAbove i 0) := by
  change Limits.WidePullback.lift (Limits.WidePullback.base (fun _ : Fin 2 => β))
      (fun j : Fin 1 => Limits.WidePullback.π (fun _ : Fin 2 => β)
        ((SimplexCategory.δ i).toOrderHom j)) (by simp)
    ≫ Limits.WidePullback.π (fun _ : Fin 1 => β) 0 = _
  rw [Limits.WidePullback.lift_π]
  congr 1

/-- The face map `δ i` of the Čech nerve is compatible with the structure maps. -/
lemma cgNerve_delta_comp_base (β : X ⟶ Y) (i : Fin 2) :
    (cgNerve β).δ i ≫ Limits.WidePullback.base (fun _ : Fin 1 => β) =
      Limits.WidePullback.base (fun _ : Fin 2 => β) := by
  change Limits.WidePullback.lift (Limits.WidePullback.base (fun _ : Fin 2 => β))
      (fun j : Fin 1 => Limits.WidePullback.π (fun _ : Fin 2 => β)
        ((SimplexCategory.δ i).toOrderHom j)) (by simp)
    ≫ Limits.WidePullback.base (fun _ : Fin 1 => β) = _
  rw [Limits.WidePullback.lift_base]

/-- The first face map of the Čech nerve is the first projection of `X ×_Y X`. -/
lemma cgNerve_delta_zero (β : X ⟶ Y) :
    (cgNerve β).δ (0 : Fin 2) = cgdelta0 β := by
  refine Limits.WidePullback.eq_lift_of_comp_eq (fun _ : Fin 1 => β) (cgbase2 β)
    (fun _ : Fin 1 => cgpi2 β 1) _ _ (fun j => ?_) (cgNerve_delta_comp_base β 0)
  have : j = (0 : Fin 1) := Subsingleton.elim j 0
  subst this
  exact cgNerve_delta_comp_pi1 β 0

/-- The second face map of the Čech nerve is the second projection of `X ×_Y X`. -/
lemma cgNerve_delta_one (β : X ⟶ Y) :
    (cgNerve β).δ (1 : Fin 2) = cgdelta1 β := by
  refine Limits.WidePullback.eq_lift_of_comp_eq (fun _ : Fin 1 => β) (cgbase2 β)
    (fun _ : Fin 1 => cgpi2 β 0) _ _ (fun j => ?_) (cgNerve_delta_comp_base β 1)
  have : j = (0 : Fin 1) := Subsingleton.elim j 0
  subst this
  exact cgNerve_delta_comp_pi1 β 1

/-! ## §2. The level-`0` term is `X` -/

/-- The canonical identification of the level-`0` term of the Čech nerve with `X`. -/
noncomputable def cgZeroIso (β : X ⟶ Y) : cgw1 β ≅ X where
  hom := cgpi1 β 0
  inv := Limits.WidePullback.lift β (fun _ : Fin 1 => 𝟙 X) (by intro j; simp)
  hom_inv_id := by
    apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
    · intro j
      rw [Category.assoc, Limits.WidePullback.lift_π]
      simp only [Category.comp_id, Category.id_comp]
      exact congrArg (fun k => cgpi1 β k) (Subsingleton.elim 0 j)
    · rw [Category.assoc, Limits.WidePullback.lift_base, Limits.WidePullback.π_arrow,
        Category.id_comp]
  inv_hom_id := Limits.WidePullback.lift_π _ _ _ _ _

lemma cgZeroIso_hom_comp_beta (β : X ⟶ Y) :
    (cgZeroIso β).hom ≫ β = cgbase1 β :=
  cgpi1_comp β

lemma cgZeroIso_inv_comp_base (β : X ⟶ Y) :
    (cgZeroIso β).inv ≫ cgbase1 β = β :=
  Limits.WidePullback.lift_base _ _ _ _

/-! ## §3. The cofork is a colimit -/

/-- An epimorphism of light condensed sets is an effective epimorphism: the category of sheaves of
types is a regular epi category. -/
lemma cgEffEpi (β : X ⟶ Y) (hβ : Epi β) : EffectiveEpi β := by
  letI := hβ
  exact (isRegularEpi_iff_effectiveEpi β).mp (IsRegularEpiCategory.regularEpiOfEpi β)

/-- The canonical `EffectiveEpiStruct` of `β`. -/
noncomputable def cgStruct (β : X ⟶ Y) (hβ : Epi β) : EffectiveEpiStruct β := by
  haveI := cgEffEpi β hβ
  exact EffectiveEpi.getStruct β

/-- The transposed "descent" map along the free/forget adjunction. -/
noncomputable def cgCoforkE (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cgdelta0 β)) ((free ℤ).map (cgdelta1 β))) :
    X ⟶ (LightCondensed.forget ℤ).obj s.pt :=
  (LightCondensed.freeForgetAdjunction ℤ).homEquiv X s.pt
    ((free ℤ).map (cgZeroIso β).inv ≫ s.π)

/-- The transpose of the free-module image of any map coequalizing the two projections
descends along `β`. -/
lemma cgCoforkE_spec (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cgdelta0 β)) ((free ℤ).map (cgdelta1 β))) :
    ∀ {Z : LightCondSet} (g₁ g₂ : Z ⟶ X), g₁ ≫ β = g₂ ≫ β →
      g₁ ≫ cgCoforkE β hβ s = g₂ ≫ cgCoforkE β hβ s := by
  intro Z g₁ g₂ hg
  -- any pair coequalizing the structure maps factors through the wide pullback `X ×_Y X`
  have key : ∀ {Z : LightCondSet} (η₀ η₁ : Z ⟶ cgw1 β), η₀ ≫ cgbase1 β = η₁ ≫ cgbase1 β →
      (free ℤ).map η₀ ≫ s.π = (free ℤ).map η₁ ≫ s.π := by
    intro Z η₀ η₁ hη
    let fs : (j : Fin 2) → Z ⟶ X :=
      fun j => Fin.cases (η₁ ≫ cgpi1 β 0) (fun _ => η₀ ≫ cgpi1 β 0) j
    have hfs : ∀ j : Fin 2, fs j ≫ β = η₀ ≫ cgbase1 β := by
      intro j
      fin_cases j
      · show (η₁ ≫ cgpi1 β 0) ≫ β = η₀ ≫ cgbase1 β
        rw [Category.assoc, cgpi1_comp, hη]
      · show (η₀ ≫ cgpi1 β 0) ≫ β = η₀ ≫ cgbase1 β
        rw [Category.assoc, cgpi1_comp]
    let ζ : Z ⟶ cgw2 β := Limits.WidePullback.lift (η₀ ≫ cgbase1 β) fs hfs
    have hζ0 : ζ ≫ cgdelta0 β = η₀ := by
      apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
      · intro j
        have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
        subst hj
        rw [Category.assoc, cgdelta0_comp_pi1, Limits.WidePullback.lift_π]
        show fs 1 = η₀ ≫ cgpi1 β 0
        rfl
      · rw [Category.assoc, cgdelta0_comp_base, Limits.WidePullback.lift_base]
    have hζ1 : ζ ≫ cgdelta1 β = η₁ := by
      apply Limits.WidePullback.hom_ext (fun _ : Fin 1 => β)
      · intro j
        have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
        subst hj
        rw [Category.assoc, cgdelta1_comp_pi1, Limits.WidePullback.lift_π]
        show fs 0 = η₁ ≫ cgpi1 β 0
        rfl
      · rw [Category.assoc, cgdelta1_comp_base, Limits.WidePullback.lift_base]
        exact hη
    rw [← hζ0, ← hζ1, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      s.condition]
  have hv : (free ℤ).map g₁ ≫ ((free ℤ).map (cgZeroIso β).inv ≫ s.π) =
      (free ℤ).map g₂ ≫ ((free ℤ).map (cgZeroIso β).inv ≫ s.π) := by
    have h1 : g₁ ≫ (cgZeroIso β).inv ≫ cgbase1 β = g₂ ≫ (cgZeroIso β).inv ≫ cgbase1 β := by
      rw [cgZeroIso_inv_comp_base, hg]
    rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    exact key _ _ h1
  calc g₁ ≫ cgCoforkE β hβ s
      = (LightCondensed.freeForgetAdjunction ℤ).homEquiv Z s.pt
          ((free ℤ).map g₁ ≫ ((free ℤ).map (cgZeroIso β).inv ≫ s.π)) :=
        (Adjunction.homEquiv_naturality_left (LightCondensed.freeForgetAdjunction ℤ) g₁ _).symm
    _ = (LightCondensed.freeForgetAdjunction ℤ).homEquiv Z s.pt
          ((free ℤ).map g₂ ≫ ((free ℤ).map (cgZeroIso β).inv ≫ s.π)) := by rw [hv]
    _ = g₂ ≫ cgCoforkE β hβ s :=
        (Adjunction.homEquiv_naturality_left (LightCondensed.freeForgetAdjunction ℤ) g₂ _)

/-- The descent map produced by the effective-epimorphism structure of `β`. -/
noncomputable def cgCoforkDesc (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cgdelta0 β)) ((free ℤ).map (cgdelta1 β))) :
    (free ℤ).obj Y ⟶ s.pt :=
  ((LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt).symm
    ((cgStruct β hβ).desc (cgCoforkE β hβ s) (cgCoforkE_spec β hβ s))

/-- Unfolding lemma for `cgCoforkDesc`. -/
lemma cgCoforkDesc_eq (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cgdelta0 β)) ((free ℤ).map (cgdelta1 β))) :
    cgCoforkDesc β hβ s =
      ((LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt).symm
        ((cgStruct β hβ).desc (cgCoforkE β hβ s) (cgCoforkE_spec β hβ s)) := rfl

/-- The factorisation property of the effective-epimorphism structure of `β`. -/
lemma cgStruct_fac (β : X ⟶ Y) (hβ : Epi β) {W : LightCondSet}
    (e : X ⟶ W)
    (h : ∀ {Z : LightCondSet} (g₁ g₂ : Z ⟶ X), g₁ ≫ β = g₂ ≫ β →
      g₁ ≫ e = g₂ ≫ e) :
    β ≫ (cgStruct β hβ).desc e h = e :=
  (cgStruct β hβ).fac e h

lemma cgCoforkDesc_fac (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cgdelta0 β)) ((free ℤ).map (cgdelta1 β))) :
    (free ℤ).map (cgbase1 β) ≫ cgCoforkDesc β hβ s = s.π := by
  have h : (LightCondensed.freeForgetAdjunction ℤ).homEquiv (cgw1 β) s.pt
        ((free ℤ).map (cgbase1 β) ≫ cgCoforkDesc β hβ s) =
      (LightCondensed.freeForgetAdjunction ℤ).homEquiv (cgw1 β) s.pt s.π := by
    rw [Adjunction.homEquiv_naturality_left, cgCoforkDesc_eq, Equiv.apply_symm_apply,
      ← cgZeroIso_hom_comp_beta β, Category.assoc, cgStruct_fac, cgCoforkE,
      ← Adjunction.homEquiv_naturality_left, ← Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((LightCondensed.freeForgetAdjunction ℤ).homEquiv (cgw1 β) s.pt).injective h

lemma cgCoforkDesc_uniq (β : X ⟶ Y) (hβ : Epi β)
    (s : Cofork ((free ℤ).map (cgdelta0 β)) ((free ℤ).map (cgdelta1 β)))
    (m : (free ℤ).obj Y ⟶ s.pt) (hm : (free ℤ).map (cgbase1 β) ≫ m = s.π) :
    m = cgCoforkDesc β hβ s := by
  have hmem : (LightCondensed.freeForgetAdjunction ℤ).homEquiv Y s.pt m =
      (cgStruct β hβ).desc (cgCoforkE β hβ s) (cgCoforkE_spec β hβ s) := by
    apply (cgStruct β hβ).uniq
    rw [← Adjunction.homEquiv_naturality_left]
    congr 1
    have hmap : (free ℤ).map (cgZeroIso β).inv ≫ (free ℤ).map (cgbase1 β) =
        (free ℤ).map β := by
      rw [← Functor.map_comp, cgZeroIso_inv_comp_base]
    rw [← hmap, Category.assoc, hm]
  rw [cgCoforkDesc_eq, ← hmem]
  exact (Equiv.symm_apply_apply _ m).symm

/-- **The Čech cofork is a colimit.**  For an epimorphism `β : X ⟶ Y` of light condensed sets,
the two face maps `ℤ[X ×_Y X] ⇉ ℤ[X]` and the augmentation have `ℤ[Y]` as their coequalizer. -/
noncomputable def cgCofork_isColimit (β : X ⟶ Y) (hβ : Epi β) :
    IsColimit (Cofork.ofπ (f := (free ℤ).map (cgdelta0 β)) (g := (free ℤ).map (cgdelta1 β))
      ((free ℤ).map (cgbase1 β)) (by
        rw [← Functor.map_comp, ← Functor.map_comp, cgdelta0_comp_base, cgdelta1_comp_base])) :=
  Cofork.IsColimit.mk _ (fun s => cgCoforkDesc β hβ s)
    (fun s => cgCoforkDesc_fac β hβ s) (fun s m hm => cgCoforkDesc_uniq β hβ s m hm)

/-- The augmented simplicial object whose alternating-face complex is the Čech complex. -/
noncomputable abbrev cgAugObj (β : X ⟶ Y) : SimplicialObject.Augmented LightCondAb :=
  (SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
    (Arrow.augmentedCechNerve (Arrow.mk β))

end

/-- Transport of the colimit property of a cofork along equalities of its two legs and of its
structure map. -/
noncomputable def cgCofork_transport {C : Type*} [Category C] {X Y P : C}
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
noncomputable def cgCofork_comp_iso {C : Type*} [Category C] {X Y P P' : C} {f g : X ⟶ Y}
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

/-- **Čech `H⁰` for an arbitrary light condensed source.**
For an epimorphism `β : X ⟶ Y` of light condensed sets, where `X` is an *arbitrary* light
condensed set (not necessarily light profinite), the degree-`0` homology map of the augmentation
`ε` of the free-module Čech complex of `β` is an isomorphism; equivalently, the cofork
`ℤ[X ×_Y X] ⇉ ℤ[X] ⟶ ℤ[Y]` given by the two face maps and the augmentation is a colimit.

The identical statement with `X` *light profinite* is proved in
`Submission/Work/ANALYTIC/CechPt/cech_h0.lean` (`Work.ANALYTIC.CechPt.cech_h0`); the whole
argument there (identifying the level-`0`/level-`1` terms of the Čech nerve, using that an
epimorphism of light condensed sets is an effective epimorphism, and building the descent map
from the effective-epimorphism structure using only the *wide pullback* structure of the nerve)
is independent of any light-profinite hypothesis on `X`; only the type of `β` changes from
`LightProfinite.toCondensed X ⟶ Y` to `X ⟶ Y`. -/
theorem cechGen_h0 {X Y : LightCondSet.{0}} (β : X ⟶ Y) (hβ : Epi β) :
    IsIso (HomologicalComplex.homologyMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
        (Arrow.augmentedCechNerve (Arrow.mk β)))) 0) := by
  let K : ChainComplex LightCondAb ℕ := AlternatingFaceMapComplex.obj (cgAugObj β).left
  let M : ChainComplex LightCondAb ℕ := (ChainComplex.single₀ LightCondAb).obj ((free ℤ).obj Y)
  let εc : K ⟶ M := AlternatingFaceMapComplex.ε.app (cgAugObj β)
  change IsIso (HomologicalComplex.homologyMap εc 0)
  -- the augmentation in degree `0` is the structure map of the level-`0` term
  have hε0 : εc.f 0 = (free ℤ).map (cgbase1 β) := by
    dsimp only [εc]
    rw [AlternatingFaceMapComplex.ε_app_f_zero]
    simp only [cgAugObj, SimplicialObject.Augmented.whiskeringObj]
    rfl
  -- the two face maps are the two projections of `X ×_Y X`
  have hδ0 : (cgAugObj β).left.δ (0 : Fin 2) = (free ℤ).map (cgdelta0 β) :=
    (show (cgAugObj β).left.δ (0 : Fin 2) =
        (free ℤ).map ((cgNerve β).δ (0 : Fin 2)) from rfl).trans
      (congrArg (fun t => (free ℤ).map t) (cgNerve_delta_zero β))
  have hδ1 : (cgAugObj β).left.δ (1 : Fin 2) = (free ℤ).map (cgdelta1 β) :=
    (show (cgAugObj β).left.δ (1 : Fin 2) =
        (free ℤ).map ((cgNerve β).δ (1 : Fin 2)) from rfl).trans
      (congrArg (fun t => (free ℤ).map t) (cgNerve_delta_one β))
  -- the augmentation coequalizes the two face maps
  have hhom : εc.f 0 = (cgAugObj β).hom.app (Opposite.op { len := 0 }) :=
    AlternatingFaceMapComplex.ε_app_f_zero (cgAugObj β)
  have hcond : (cgAugObj β).left.δ (0 : Fin 2) ≫ εc.f 0 =
      (cgAugObj β).left.δ (1 : Fin 2) ≫ εc.f 0 := by
    have step1 : (cgAugObj β).left.δ (0 : Fin 2) ≫ εc.f 0 =
        (cgAugObj β).left.δ (0 : Fin 2) ≫
          (cgAugObj β).hom.app (Opposite.op { len := 0 }) :=
      congrArg (fun t => (cgAugObj β).left.δ (0 : Fin 2) ≫ t) hhom
    have step2 : (cgAugObj β).left.δ (0 : Fin 2) ≫
          (cgAugObj β).hom.app (Opposite.op { len := 0 }) =
        (cgAugObj β).hom.app (Opposite.op { len := 1 }) :=
      (SimplicialObject.δ_naturality (f := (cgAugObj β).hom) (n := 0)
        (0 : Fin 2)).trans (Category.comp_id _)
    have step3 : (cgAugObj β).hom.app (Opposite.op { len := 1 }) =
        (cgAugObj β).left.δ (1 : Fin 2) ≫
          (cgAugObj β).hom.app (Opposite.op { len := 0 }) :=
      ((SimplicialObject.δ_naturality (f := (cgAugObj β).hom) (n := 0)
        (1 : Fin 2)).trans (Category.comp_id _)).symm
    have step4 : (cgAugObj β).left.δ (1 : Fin 2) ≫
          (cgAugObj β).hom.app (Opposite.op { len := 0 }) =
        (cgAugObj β).left.δ (1 : Fin 2) ≫ εc.f 0 :=
      (congrArg (fun t => (cgAugObj β).left.δ (1 : Fin 2) ≫ t) hhom).symm
    exact step1.trans (step2.trans (step3.trans step4))
  -- the cofork of the two face maps is a colimit
  have hc : IsColimit (Cofork.ofπ (f := (cgAugObj β).left.δ (0 : Fin 2))
      (g := (cgAugObj β).left.δ (1 : Fin 2)) (εc.f 0) hcond) :=
    cgCofork_transport hδ0.symm hδ1.symm hε0.symm
      (cgCofork_isColimit β hβ)
  -- `K.d 1 0` is the difference of the two face maps, so its cokernel projection coequalizes them
  have hKd : K.d 1 0 = (cgAugObj β).left.δ (0 : Fin 2) - (cgAugObj β).left.δ (1 : Fin 2) := by
    have h : K.d 1 0 = ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (cgAugObj β).left.δ i := by
      rw [AlternatingFaceMapComplex.obj_d_eq]
    rw [h, Fin.sum_univ_two, sub_eq_add_neg]
    simp
  have hpO_cond : (cgAugObj β).left.δ (0 : Fin 2) ≫ K.pOpcycles 0 =
      (cgAugObj β).left.δ (1 : Fin 2) ≫ K.pOpcycles 0 := by
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
  have hcondπ : (cgAugObj β).left.δ (0 : Fin 2) ≫ π' =
      (cgAugObj β).left.δ (1 : Fin 2) ≫ π' := by
    dsimp only [π']
    rw [← Category.assoc, ← Category.assoc, hcond]
  -- the Čech cofork with the twisted structure map is a colimit as well
  have hcπ : IsColimit (Cofork.ofπ (f := (cgAugObj β).left.δ (0 : Fin 2))
      (g := (cgAugObj β).left.δ (1 : Fin 2)) π' hcondπ) :=
    cgCofork_comp_iso x hc
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

end Work.ANALYTIC.CechGen
