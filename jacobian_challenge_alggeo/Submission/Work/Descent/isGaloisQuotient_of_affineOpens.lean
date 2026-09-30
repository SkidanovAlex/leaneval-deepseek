import Mathlib
import Submission.Work.Descent.Scheme

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

open scoped AlgebraicGeometry

universe u

namespace Work.Descent

/-
Support material for `Work.Descent.isGaloisQuotient_of_affineOpens`: base change of morphisms of
`k`-schemes along `Spec k' ⟶ Spec k`, the base change `U_{k'} ⟶ X_{k'}` of an open subscheme, and
the "local on `X`" principle for morphisms out of `X_{k'}`.

The declarations are collected in the namespace `Work.Descent.AffOpensDesc` to avoid clashes with
the other developments of area DS.
-/

namespace AffOpensDesc

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- The morphism `Y_{k'} ⟶ Z_{k'}` of underlying schemes induced by a morphism `f : Y ⟶ Z` of
`k`-schemes: the pullback of `f` along `Spec k' ⟶ Spec k`, realized as the canonical lift. -/
noncomputable def baseChangeHom {X Y : Sch k} (f : X ⟶ Y) :
    (baseChange (k := k) (k' := k') X).left ⟶ (baseChange (k := k) (k' := k') Y).left :=
  pullback.lift (pullback.fst X.hom (specMap k k') ≫ f.left)
    (pullback.snd X.hom (specMap k k')) (by
      rw [Category.assoc, Over.w f]
      exact baseChangeπ_hom X)

@[reassoc (attr := simp)]
lemma baseChangeHom_fst {X Y : Sch k} (f : X ⟶ Y) :
    baseChangeHom (k := k) (k' := k') f ≫ pullback.fst Y.hom (specMap k k') =
      pullback.fst X.hom (specMap k k') ≫ f.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeHom_snd {X Y : Sch k} (f : X ⟶ Y) :
    baseChangeHom (k := k) (k' := k') f ≫ pullback.snd Y.hom (specMap k k') =
      pullback.snd X.hom (specMap k k') :=
  pullback.lift_snd _ _ _

lemma baseChangeHom_comp {X Y Z : Sch k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChangeHom (k := k) (k' := k') (f ≫ g) =
      baseChangeHom f ≫ baseChangeHom g := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, baseChangeHom_fst, baseChangeHom_fst_assoc, baseChangeHom_snd,
      baseChangeHom_snd_assoc, Over.comp_left]

@[reassoc (attr := simp)]
lemma galAct_fst (X : Sch k) (σ : Gal k k') :
    galAct (k := k) (k' := k') X σ ≫ pullback.fst X.hom (specMap k k') =
      pullback.fst X.hom (specMap k k') :=
  galAct_π X σ

@[reassoc (attr := simp)]
lemma galAct_snd (X : Sch k) (σ : Gal k k') :
    galAct (k := k) (k' := k') X σ ≫ pullback.snd X.hom (specMap k k') =
      pullback.snd X.hom (specMap k k') ≫ Spec.map (CommRingCat.ofHom (σ : k' →+* k')) := by
  simp [galAct, pullback.map, pullback.lift_snd]

/-- Base change of morphisms commutes with the Galois action. -/
lemma galAct_baseChangeHom {X Y : Sch k} (f : X ⟶ Y) (σ : Gal k k') :
    galAct (k := k) (k' := k') X σ ≫ baseChangeHom (k := k) (k' := k') f =
      baseChangeHom f ≫ galAct (k := k) (k' := k') Y σ := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, galAct_fst, galAct_fst_assoc, galAct_snd, galAct_snd_assoc,
      baseChangeHom_fst, baseChangeHom_fst_assoc, baseChangeHom_snd, baseChangeHom_snd_assoc]

/-- The open subscheme `U` of `X`, as a `k`-scheme over `X`. -/
noncomputable def thetaOver {X : Sch k} (U : X.left.Opens) :
    (Over.mk (U.ι ≫ X.hom)) ⟶ X :=
  Over.homMk U.ι rfl

/-- The base change `U_{k'} ⟶ X_{k'}` of an open subscheme `U` of `X`, as a morphism of
underlying schemes. -/
noncomputable def theta {X : Sch k} (U : X.left.Opens) :
    (baseChange (k := k) (k' := k') (Over.mk (U.ι ≫ X.hom))).left ⟶
      (baseChange (k := k) (k' := k') X).left :=
  baseChangeHom (k := k) (k' := k') (thetaOver U)

/-- The morphism of `k`-schemes `U ⟶ V` induced by an inclusion `U ≤ V` of open subschemes. -/
noncomputable def thetaHom {X : Sch k} {W U : X.left.Opens} (h : W ≤ U) :
    (Over.mk (W.ι ≫ X.hom)) ⟶ (Over.mk (U.ι ≫ X.hom)) :=
  Over.homMk (X.left.homOfLE h)
    (by change X.left.homOfLE h ≫ (U.ι ≫ X.hom) = W.ι ≫ X.hom
        rw [← Category.assoc, Scheme.homOfLE_ι])

lemma baseChangeHom_thetaHom_fst {X : Sch k} {W U : X.left.Opens} (h : W ≤ U) :
    baseChangeHom (k := k) (k' := k') (thetaHom h) ≫ pullback.fst (U.ι ≫ X.hom) (specMap k k') =
      pullback.fst (W.ι ≫ X.hom) (specMap k k') ≫ X.left.homOfLE h :=
  baseChangeHom_fst _

@[reassoc (attr := simp)]
lemma theta_fst {X : Sch k} (U : X.left.Opens) :
    theta (k := k) (k' := k') U ≫ pullback.fst X.hom (specMap k k') =
      pullback.fst (U.ι ≫ X.hom) (specMap k k') ≫ U.ι :=
  baseChangeHom_fst _

@[reassoc (attr := simp)]
lemma theta_snd {X : Sch k} (U : X.left.Opens) :
    theta (k := k) (k' := k') U ≫ pullback.snd X.hom (specMap k k') =
      pullback.snd (U.ι ≫ X.hom) (specMap k k') :=
  baseChangeHom_snd _

/-- Restriction to open subschemes is compatible with the Galois action. -/
lemma galAct_theta {X : Sch k} (U : X.left.Opens) (σ : Gal k k') :
    galAct (k := k) (k' := k') (Over.mk (U.ι ≫ X.hom)) σ ≫ theta (k := k) (k' := k') U =
      theta (k := k) (k' := k') U ≫ galAct (k := k) (k' := k') X σ := by
  rw [theta]
  exact galAct_baseChangeHom (X := Over.mk (U.ι ≫ X.hom)) (Y := X) (Over.homMk U.ι rfl) σ

lemma thetaOver_comp {X : Sch k} {W U : X.left.Opens} (h : W ≤ U) :
    thetaOver W = thetaHom h ≫ thetaOver U := by
  rw [thetaOver, thetaOver]
  rw [thetaHom]
  rw [← Over.homMk_comp]
  simp only [Scheme.homOfLE_ι]

/-- Restriction to open subschemes is functorial. -/
lemma theta_homOfLE {X : Sch k} {W U : X.left.Opens} (h : W ≤ U) :
    theta (k := k) (k' := k') W =
      baseChangeHom (k := k) (k' := k') (thetaHom h) ≫ theta (k := k) (k' := k') U := by
  rw [theta, theta, ← baseChangeHom_comp, thetaOver_comp h]

/-- The restriction `U_{k'} ⟶ X_{k'}` identifies `U_{k'}` with the pullback of the open
immersion `U.ι` along `X_{k'} ⟶ X`. -/
noncomputable def thetaIso {X : Sch k} (U : X.left.Opens) :
    pullback (U.ι ≫ X.hom) (specMap k k') ≅
      pullback (pullback.fst X.hom (specMap k k')) U.ι :=
  (pullbackRightPullbackFstIso X.hom (specMap k k') U.ι).symm ≪≫
    (pullbackSymmetry U.ι (pullback.fst X.hom (specMap k k')))

lemma thetaIso_hom_fst {X : Sch k} (U : X.left.Opens) :
    (thetaIso (k := k) (k' := k') U).hom ≫
      pullback.fst (pullback.fst X.hom (specMap k k')) U.ι = theta U := by
  rw [thetaIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst, theta_fst]
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd, theta_snd]

/-- A morphism out of `X_{k'}` is determined by its restrictions to the preimages of the affine
open subschemes of `X`. -/
theorem eq_of_theta_comp_eq {X : Sch k} {Z : Scheme}
    (a b : (baseChange (k := k) (k' := k') X).left ⟶ Z)
    (h : ∀ (U : X.left.Opens), IsAffineOpen U → theta U ≫ a = theta U ≫ b) : a = b := by
  let 𝒱 : (baseChange (k := k) (k' := k') X).left.OpenCover :=
    (X.left.directedAffineCover).pullback₁ (baseChangeπ X)
  refine 𝒱.hom_ext a b (fun U => ?_)
  let U' : X.left.affineOpens := U
  change pullback.fst (pullback.fst X.hom (specMap k k')) U'.1.ι ≫ a =
    pullback.fst (pullback.fst X.hom (specMap k k')) U'.1.ι ≫ b
  have hcancel : (thetaIso (k := k) (k' := k') U'.1).hom ≫
      (pullback.fst (pullback.fst X.hom (specMap k k')) U'.1.ι ≫ a) =
      (thetaIso (k := k) (k' := k') U'.1).hom ≫
        (pullback.fst (pullback.fst X.hom (specMap k k')) U'.1.ι ≫ b) := by
    rw [← Category.assoc, thetaIso_hom_fst]
    rw [← Category.assoc, thetaIso_hom_fst]
    exact h U'.1 U'.2
  exact (cancel_epi (thetaIso (k := k) (k' := k') U'.1).hom).mp hcancel


end AffOpensDesc

open AffOpensDesc

theorem isGaloisQuotient_of_affineOpens {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (X : Work.Descent.Sch k)
    (h : ∀ (U : X.left.Opens), AlgebraicGeometry.IsAffineOpen U →
      Work.Descent.IsGaloisQuotient k k'
        (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.comp U.ι X.hom))) :
    Work.Descent.IsGaloisQuotient k k' X := by
  intro Y Φ hΦ hInv
  have hΦ' : Φ ≫ Y.hom = pullback.snd X.hom (specMap k k') ≫ specMap k k' := hΦ
  -- On every affine open subscheme the restriction of `Φ` factors uniquely through `U_{k'} ⟶ U`.
  have key : ∀ U : X.left.affineOpens,
      ∃ g : (Over.mk (U.1.ι ≫ X.hom)) ⟶ Y,
        baseChangeπ (Over.mk (U.1.ι ≫ X.hom)) ≫ g.left =
          theta (k := k) (k' := k') U.1 ≫ Φ ∧
        ∀ g' : (Over.mk (U.1.ι ≫ X.hom)) ⟶ Y,
          baseChangeπ (Over.mk (U.1.ι ≫ X.hom)) ≫ g'.left = theta U.1 ≫ Φ → g' = g := by
    intro U
    refine h U.1 U.2 Y (theta (k := k) (k' := k') U.1 ≫ Φ) ?_ ?_
    · change (theta (k := k) (k' := k') U.1 ≫ Φ) ≫ Y.hom =
        pullback.snd (U.1.ι ≫ X.hom) (specMap k k') ≫ specMap k k'
      rw [Category.assoc, hΦ']
      rw [← Category.assoc, theta_snd]
    · intro σ
      rw [← Category.assoc]
      rw [galAct_theta U.1 σ]
      rw [Category.assoc]
      rw [hInv σ]
  choose g hg huniq using key
  -- The factorizations are compatible on inclusions of affine open subschemes.
  have hcompat : ∀ {U V : X.left.affineOpens} (hUV : U ≤ V),
      X.left.homOfLE hUV ≫ (g V).left = (g U).left := by
    intro U V hUV
    have hUφ : thetaHom hUV ≫ g V = g U := by
      have hfac : baseChangeHom (k := k) (k' := k') (thetaHom hUV) ≫
          baseChangeπ (Over.mk (V.1.ι ≫ X.hom)) =
          baseChangeπ (Over.mk (U.1.ι ≫ X.hom)) ≫ X.left.homOfLE hUV :=
        baseChangeHom_thetaHom_fst hUV
      have hθ : theta (k := k) (k' := k') U.1 =
          baseChangeHom (k := k) (k' := k') (thetaHom hUV) ≫
            theta (k := k) (k' := k') V.1 := theta_homOfLE hUV
      refine huniq U (thetaHom hUV ≫ g V) ?_
      rw [Over.comp_left]
      change baseChangeπ (Over.mk (U.1.ι ≫ X.hom)) ≫
        (X.left.homOfLE hUV ≫ (g V).left) = theta U.1 ≫ Φ
      rw [← Category.assoc]
      rw [← hfac]
      rw [Category.assoc]
      rw [hg V]
      rw [← Category.assoc]
      rw [← hθ]
    have h2 := congrArg Over.Hom.left hUφ
    rw [Over.comp_left] at h2
    change X.left.homOfLE hUV ≫ (g V).left = (g U).left at h2
    exact h2
  -- Glue the local factorizations to a morphism `X ⟶ Y`.
  have hw : ∀ U : X.left.affineOpens, (g U).left ≫ Y.hom =
      X.left.directedAffineCover.f U ≫ X.hom := fun U => Over.w (g U)
  have hcomp : ∀ {U V : X.left.affineOpens} (hij : U ⟶ V),
      X.left.directedAffineCover.trans hij ≫ (g V).left = (g U).left := fun {U V} hij => by
    change X.left.homOfLE (leOfHom hij) ≫ (g V).left = (g U).left
    exact hcompat (leOfHom hij)
  let g₀ : X ⟶ Y := X.left.directedAffineCover.glueMorphismsOverOfLocallyDirected
    (fun U => (g U).left) hcomp hw
  have hglue : ∀ U : X.left.affineOpens, U.1.ι ≫ g₀.left = (g U).left := by
    intro U
    change X.left.directedAffineCover.f U ≫ g₀.left = (g U).left
    exact X.left.directedAffineCover.map_glueMorphismsOverOfLocallyDirected_left _ _ _ U
  have hmain : baseChangeπ (k := k) (k' := k') X ≫ g₀.left = Φ := by
    refine eq_of_theta_comp_eq _ _ (fun U hU => ?_)
    rw [← Category.assoc]
    change (theta (k := k) (k' := k') U ≫ pullback.fst X.hom (specMap k k')) ≫ g₀.left =
      theta U ≫ Φ
    rw [theta_fst]
    rw [Category.assoc]
    rw [hglue ⟨U, hU⟩]
    exact hg ⟨U, hU⟩
  refine ⟨g₀, hmain, ?_⟩
  intro g' hg'
  apply Over.OverMorphism.ext
  refine X.left.directedAffineCover.hom_ext g'.left g₀.left (fun U => ?_)
  have hg'' : pullback.fst X.hom (specMap k k') ≫ g'.left = Φ := hg'
  have hUι : thetaOver U.1 ≫ g' = g U := by
    refine huniq U _ ?_
    rw [Over.comp_left]
    change baseChangeπ (Over.mk (U.1.ι ≫ X.hom)) ≫ (U.1.ι ≫ g'.left) = theta U.1 ≫ Φ
    rw [← Category.assoc]
    change (pullback.fst (U.1.ι ≫ X.hom) (specMap k k') ≫ U.1.ι) ≫ g'.left = theta U.1 ≫ Φ
    rw [← theta_fst]
    rw [Category.assoc]
    change theta U.1 ≫ (pullback.fst X.hom (specMap k k') ≫ g'.left) = theta U.1 ≫ Φ
    rw [hg'']
  have h1 : U.1.ι ≫ g'.left = (g U).left := by
    have h := congrArg Over.Hom.left hUι
    rw [Over.comp_left] at h
    change U.1.ι ≫ g'.left = (g U).left at h
    exact h
  change U.1.ι ≫ g'.left = U.1.ι ≫ g₀.left
  rw [h1, hglue U]


end Work.Descent
