import Mathlib
import Submission.Work.SymQuot.Sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# `Symⁿ C` is geometrically irreducible (area SY, target of `Sym.geometricallyIrreducible_sym`)

The symmetric power `Symⁿ C` of a curve is the quotient of `Cⁿ` by the action of `S_n`
(area `SY`).  Two facts are used:

* `Cⁿ` is geometrically irreducible over `K`: the structure morphism of `Cⁿ` is a composite of
  base changes of `C.hom`, and geometric irreducibility is stable under base change and
  composition (`GeometricallyIrreducible.comp`, which needs `UniversallyOpen` — here automatic
  because `C` is smooth over a field);
* the quotient map `Cⁿ ⟶ Symⁿ C` is surjective (`Sym.quot_surjective`), and a base change of a
  surjective morphism is surjective, so `Symⁿ C ×_K Spec L` is a continuous image of the
  irreducible `Cⁿ ×_K Spec L`.

Everything is proved for an arbitrary `K`-scheme `X` with `X.hom` geometrically irreducible and
universally open (in particular for `X = C.toOver`).
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Sym

/-! ## General facts on geometric irreducibility -/

/-- Geometric irreducibility is invariant under precomposition with an isomorphism. -/
lemma geometricallyIrreducible_of_iso_comp {X' X S : Scheme.{u}} (e : X' ≅ X) (g : X ⟶ S)
    (h : GeometricallyIrreducible g) : GeometricallyIrreducible (e.hom ≫ g) := by
  refine ⟨fun K _ y Z fst snd hpb => ?_⟩
  exact h.geometrically_irreducibleSpace (K := K) y (Z := Z) (fst ≫ e.hom) snd
    (hpb.of_iso (Iso.refl Z) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp))

/-- An isomorphism onto `Spec K`, for `K` a field, is geometrically irreducible: its base change
along `Spec L ⟶ Spec K` is an isomorphism onto `Spec L`, which is irreducible. -/
lemma geometricallyIrreducible_of_isIso_spec {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIso f] : GeometricallyIrreducible f := by
  refine ⟨fun L _ y Z fst snd hpb => ?_⟩
  haveI : IsIso snd := hpb.isIso_snd_of_isIso
  exact (Homeomorph.irreducibleSpace_iff snd.homeomorph).mpr inferInstance

/-- Geometric irreducibility passes to the target of a surjective morphism: if `u ≫ v` is
geometrically irreducible and `u` is surjective, then so is `v`.

Indeed, for any field `L` and `y : Spec L ⟶ S` the induced map
`pullback (u ≫ v) y ⟶ pullback v y` is the base change of `u` along `pullback.fst v y`
(`pullbackRightPullbackFstIso`), hence surjective, and a continuous image of an irreducible
space is irreducible. -/
lemma geometricallyIrreducible_of_surjective {X Y S : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ S)
    [Surjective u] (h : GeometricallyIrreducible (u ≫ v)) : GeometricallyIrreducible v := by
  rw [GeometricallyIrreducible.eq_geometrically, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have h' : IrreducibleSpace ↥(pullback (u ≫ v) y) :=
    h.geometrically_irreducibleSpace (K := K) y (Z := pullback (u ≫ v) y)
      (pullback.fst (u ≫ v) y) (pullback.snd (u ≫ v) y) (IsPullback.of_hasPullback _ _)
  let ψ : pullback (u ≫ v) y ⟶ pullback v y :=
    (pullbackRightPullbackFstIso v y u).inv ≫ pullback.snd u (pullback.fst v y)
  haveI : Surjective ψ := inferInstance
  exact ψ.surjective.irreducibleSpace ψ.continuous

/-! ## The powers `Xⁿ` -/

/-- The empty power `X⁰` is the terminal object of `Over (Spec K)`, so its structure morphism
is an isomorphism. -/
lemma isIso_prod_zero {K : Type u} [Field K] (X : Work.GCBasics.Sch K) :
    IsIso (∏ᶜ (fun _ : Fin 0 => X)).hom := by
  have hT : IsTerminal (∏ᶜ (fun _ : Fin 0 => X)) :=
    Equiv.toFun (isLimitEquivIsTerminalOfIsEmpty (Work.GCBasics.Sch K)
      (limit.cone (Discrete.functor (fun _ : Fin 0 => X)))) (limit.isLimit _)
  let T := ∏ᶜ (fun _ : Fin 0 => X)
  let g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ T := hT.from _
  let f : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk T.hom (by simp)
  have h1 : f ≫ g = 𝟙 T := hT.hom_ext (f ≫ g) (𝟙 T)
  have h2 : g.left ≫ T.hom = 𝟙 (Spec (CommRingCat.of K)) := Over.w g
  have h3 : T.hom ≫ g.left = 𝟙 T.left := congrArg (fun φ : T ⟶ T => φ.left) h1
  exact ⟨g.left, h3, h2⟩

/-- The structure morphism of a binary product of universally open `K`-schemes is universally
open: `(Y ⨯ Z).hom = fst ≫ Y.hom` is a base change of `Z.hom` followed by `Y.hom`. -/
lemma universallyOpen_prod_binary {K : Type u} [Field K] (Y Z : Work.GCBasics.Sch K)
    [UniversallyOpen Y.hom] [UniversallyOpen Z.hom] : UniversallyOpen (Y ⨯ Z).hom := by
  have hkey : (Over.prodLeftIsoPullback Y Z).hom ≫ (pullback.fst Y.hom Z.hom ≫ Y.hom) =
      (Y ⨯ Z).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.w]
  rw [← hkey]
  exact inferInstance

/-- The structure morphism of `Xⁿ` is universally open if `X` is universally open over `K`. -/
lemma universallyOpen_prod {K : Type u} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ)
    [UniversallyOpen X.hom] : UniversallyOpen (Work.SymQuot.prod X n).hom := by
  change UniversallyOpen (∏ᶜ (fun _ : Fin n => X)).hom
  induction n with
  | zero =>
    haveI : IsIso (∏ᶜ (fun _ : Fin 0 => X)).hom := isIso_prod_zero X
    exact inferInstance
  | succ n ih =>
    haveI : UniversallyOpen (∏ᶜ (fun _ : Fin n => X)).hom := ih
    have hbin : UniversallyOpen ((∏ᶜ (fun _ : Fin n => X)) ⨯ X).hom :=
      universallyOpen_prod_binary _ _
    rw [← Over.w (Work.SymQuot.Prod.prodSuccIso X n).hom]
    exact inferInstance

/-- A binary product of geometrically irreducible `K`-schemes (with universally open structure
morphisms) is geometrically irreducible over `K`: its structure morphism is the base change
`pullback.fst Y.hom Z.hom` of `Z.hom`, followed by `Y.hom`. -/
lemma geometricallyIrreducible_prod_binary {K : Type u} [Field K] (Y Z : Work.GCBasics.Sch K)
    [GeometricallyIrreducible Y.hom] [GeometricallyIrreducible Z.hom]
    [UniversallyOpen Y.hom] [UniversallyOpen Z.hom] : GeometricallyIrreducible (Y ⨯ Z).hom := by
  have h1 : GeometricallyIrreducible (pullback.fst Y.hom Z.hom ≫ Y.hom) :=
    GeometricallyIrreducible.comp (pullback.fst Y.hom Z.hom) Y.hom
  have hkey : (Over.prodLeftIsoPullback Y Z).hom ≫ (pullback.fst Y.hom Z.hom ≫ Y.hom) =
      (Y ⨯ Z).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.w]
  rw [← hkey]
  exact geometricallyIrreducible_of_iso_comp (Over.prodLeftIsoPullback Y Z) _ h1

/-- **The `n`-fold power of a geometrically irreducible, universally open `K`-scheme is
geometrically irreducible over `K`.** -/
lemma geometricallyIrreducible_prod {K : Type u} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ)
    [GeometricallyIrreducible X.hom] [UniversallyOpen X.hom] :
    GeometricallyIrreducible (Work.SymQuot.prod X n).hom := by
  change GeometricallyIrreducible (∏ᶜ (fun _ : Fin n => X)).hom
  induction n with
  | zero =>
    haveI : IsIso (∏ᶜ (fun _ : Fin 0 => X)).hom := isIso_prod_zero X
    exact geometricallyIrreducible_of_isIso_spec _
  | succ n ih =>
    haveI : UniversallyOpen (∏ᶜ (fun _ : Fin n => X)).hom := universallyOpen_prod X n
    have hbin : GeometricallyIrreducible ((∏ᶜ (fun _ : Fin n => X)) ⨯ X).hom :=
      geometricallyIrreducible_prod_binary _ _
    rw [← Over.w (Work.SymQuot.Prod.prodSuccIso X n).hom]
    exact geometricallyIrreducible_of_iso_comp
      ((Over.forget (Spec (CommRingCat.of K))).mapIso (Work.SymQuot.Prod.prodSuccIso X n)) _ hbin

/-- **`Symⁿ C` is geometrically irreducible over `K`.**

`Sym.quot : Cⁿ ⟶ Symⁿ C` is surjective and `Cⁿ` is geometrically irreducible over `K`, so
`Symⁿ C` is, by `geometricallyIrreducible_of_surjective`. -/
theorem geometricallyIrreducible_sym {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) : AlgebraicGeometry.GeometricallyIrreducible (Work.SymQuot.Sym C n).hom := by
  haveI : Surjective (Work.SymQuot.Sym.quot C n).left :=
    ⟨Work.SymQuot.Sym.quot_surjective C n⟩
  refine geometricallyIrreducible_of_surjective (Work.SymQuot.Sym.quot C n).left
    (Work.SymQuot.Sym C n).hom ?_
  rw [Work.SymQuot.Sym.quot_hom]
  exact geometricallyIrreducible_prod C.toOver n

end Work.SymQuot.Sym
