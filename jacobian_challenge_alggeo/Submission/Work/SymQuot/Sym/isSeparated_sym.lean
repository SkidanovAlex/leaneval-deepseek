/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Symⁿ C` is separated over `K` (area SY)

The `n`-th symmetric power `Symⁿ C = Cⁿ/S_n` of a curve is separated over `K`.

## Strategy

Write `X := Cⁿ`, `Q := Symⁿ C`, `q : X ⟶ Q` for the quotient map, `g : Q ⟶ Spec K` and
`f := q ≫ g : X ⟶ Spec K` for the structure morphisms.  Since `IsSeparated g` is by definition
the statement that the diagonal `Δ_g : Q ⟶ Q ×_K Q` is a closed immersion
(`IsClosedImmersion (pullback.diagonal g)`), and since `Δ_g` is always an immersion
(`instIsImmersion`), it remains to see that `Set.range (pullback.diagonal g)` is closed.

The diagonal of `Q` is obtained from the diagonal of `X` by the "product" map `q ×_K q`:
`q ≫ Δ_g = Δ_f ≫ (q ×_K q)` (`pullback.comp_diagonal`).  Since `q` is surjective, this gives

  `Set.range Δ_g = (q ×_K q) '' Set.range Δ_f`.

Now `Set.range Δ_f` is closed because `X = Cⁿ` is proper (hence separated) over `K`
(`SymQuot.Prod.isProper_prod`), and `q ×_K q` is a closed map: it factors as
`X ×_K X --(q × id)--> Q ×_K X --(id × q)--> Q ×_K Q`, the composite of two base changes of the
universally closed morphism `q` (the quotient map is integral,
`SymQuot.Chart.quotientMap_isIntegralHom`, hence universally closed).
-/
import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Prod.isProper_prod
import Submission.Work.SymQuot.Chart.quotientMap_isIntegralHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.Sym

/-! ## Auxiliary lemmas: `q ×_K q` is a closed map

Let `q : X ⟶ Q`, `g : Q ⟶ S` and `f : X ⟶ S` satisfy `q ≫ g = f`.  Then the "product"
`q ×_S q : X ×_S X ⟶ Q ×_S Q` is the composite of the two base changes

  `X ×_S X --(q × id)--> Q ×_S X --(id × q)--> Q ×_S Q`

of `q`, so it is closed as soon as `q` is universally closed.
-/

section ClosedProduct

variable {X Q S : Scheme} (q : X ⟶ Q) (g : Q ⟶ S) (f : X ⟶ S) (h : q ≫ g = f)

/-- The first half `q × id_X : X ×_S X ⟶ Q ×_S X` of the product `q ×_S q` is a base change
of `q` along `pullback.fst g f : Q ×_S X ⟶ Q`. -/
theorem isPullback_fst_pullbackMap :
    IsPullback (pullback.fst f f)
      (pullback.map f f g f q (𝟙 X) (𝟙 S) (by simp [h]) (by simp)) q (pullback.fst g f) := by
  have hρfst : (pullback.map f f g f q (𝟙 X) (𝟙 S) (by simp [h]) (by simp)) ≫ pullback.fst g f
      = pullback.fst f f ≫ q := by
    simp only [pullback.map]; rw [pullback.lift_fst]
  have hρsnd : (pullback.map f f g f q (𝟙 X) (𝟙 S) (by simp [h]) (by simp)) ≫ pullback.snd g f
      = pullback.snd f f := by
    simp only [pullback.map]; rw [pullback.lift_snd, Category.comp_id]
  refine IsPullback.of_bot (s := ?_) (p := hρfst.symm) (t := IsPullback.of_hasPullback g f)
  rw [hρsnd, h]
  exact IsPullback.of_hasPullback f f

/-- The second half `id_Q × q : Q ×_S X ⟶ Q ×_S Q` of the product `q ×_S q` is a base change
of `q` along `pullback.snd g g : Q ×_S Q ⟶ Q`. -/
theorem isPullback_snd_pullbackMap :
    IsPullback (pullback.snd g f)
      (pullback.map g f g g (𝟙 Q) q (𝟙 S) (by simp) (by simp [h])) q (pullback.snd g g) := by
  have hρfst : (pullback.map g f g g (𝟙 Q) q (𝟙 S) (by simp) (by simp [h])) ≫ pullback.fst g g
      = pullback.fst g f := by
    simp only [pullback.map]; rw [pullback.lift_fst, Category.comp_id]
  have hρsnd : (pullback.map g f g g (𝟙 Q) q (𝟙 S) (by simp) (by simp [h])) ≫ pullback.snd g g
      = pullback.snd g f ≫ q := by
    simp only [pullback.map]; rw [pullback.lift_snd]
  refine IsPullback.of_bot (s := ?_) (p := hρsnd.symm) (t := (IsPullback.of_hasPullback g g).flip)
  rw [hρfst, h]
  exact (IsPullback.of_hasPullback g f).flip

/-- **The product `q ×_S q` of a universally closed morphism with itself is a closed map.** -/
theorem isClosedMap_pullbackMap (hq : UniversallyClosed q) :
    IsClosedMap ⇑(pullback.map f f g g q q (𝟙 S) (by simp [h]) (by simp [h])) := by
  haveI : UniversallyClosed (pullback.map f f g f q (𝟙 X) (𝟙 S) (by simp [h]) (by simp)) :=
    MorphismProperty.of_isPullback (isPullback_fst_pullbackMap q g f h) hq
  haveI : UniversallyClosed (pullback.map g f g g (𝟙 Q) q (𝟙 S) (by simp) (by simp [h])) :=
    MorphismProperty.of_isPullback (isPullback_snd_pullbackMap q g f h) hq
  have h₁ : IsClosedMap ⇑(pullback.map f f g f q (𝟙 X) (𝟙 S) (by simp [h]) (by simp)) :=
    Scheme.Hom.isClosedMap _
  have h₂ : IsClosedMap ⇑(pullback.map g f g g (𝟙 Q) q (𝟙 S) (by simp) (by simp [h])) :=
    Scheme.Hom.isClosedMap _
  have hqq : (pullback.map f f g f q (𝟙 X) (𝟙 S) (by simp [h]) (by simp)) ≫
      (pullback.map g f g g (𝟙 Q) q (𝟙 S) (by simp) (by simp [h]))
      = pullback.map f f g g q q (𝟙 S) (by simp [h]) (by simp [h]) := by
    have hc := pullback.map_comp (f := f) (g := f) (f' := g) (g' := f) (f'' := g) (g'' := g)
      (i₁ := q) (j₁ := 𝟙 Q) (i₂ := 𝟙 X) (j₂ := q) (i₃ := 𝟙 S) (j₃ := 𝟙 S)
      (by simp [h]) (by simp) (by simp) (by simp [h])
    simpa using hc
  have hqq' : ⇑(pullback.map f f g g q q (𝟙 S) (by simp [h]) (by simp [h])) =
      ⇑(pullback.map g f g g (𝟙 Q) q (𝟙 S) (by simp) (by simp [h])) ∘
      ⇑(pullback.map f f g f q (𝟙 X) (𝟙 S) (by simp [h]) (by simp)) := by
    rw [← hqq]; rfl
  rw [hqq']
  exact IsClosedMap.comp h₂ h₁

end ClosedProduct

theorem isSeparated_sym {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) :
    AlgebraicGeometry.IsSeparated (Work.SymQuot.Sym C n).hom := by
  -- `q ≫ g = f`, where `q` is the quotient map, `g` the structure morphism of `Symⁿ C`
  -- and `f` the structure morphism of `Cⁿ`.
  have hF : (Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom
      = (Work.SymQuot.prod C.toOver n).hom := Work.SymQuot.Sym.quot_hom C n
  have hsurj : Function.Surjective ⇑(Work.SymQuot.Sym.quot C n).left :=
    Work.SymQuot.Sym.quot_surjective C n
  -- `Cⁿ` is proper, hence separated, over `K`
  have hFsep : IsSeparated
      ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom) := by
    rw [hF]
    exact (Work.SymQuot.Prod.isProper_prod C.toOver n).toIsSeparated
  -- the quotient map is integral, hence universally closed
  have hq_uc : UniversallyClosed (Work.SymQuot.Sym.quot C n).left := by
    haveI : IsIntegralHom (Work.SymQuot.Sym.quot C n).left :=
      Work.SymQuot.Chart.quotientMap_isIntegralHom (Work.SymQuot.symData C n)
    infer_instance
  -- the product `q ×_K q` is a closed map
  have hclosedqq : IsClosedMap ⇑(pullback.map
      ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
      ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
      (Work.SymQuot.Sym C n).hom (Work.SymQuot.Sym C n).hom
      (Work.SymQuot.Sym.quot C n).left (Work.SymQuot.Sym.quot C n).left
      (𝟙 (Spec (CommRingCat.of K))) (by simp) (by simp)) :=
    isClosedMap_pullbackMap (Work.SymQuot.Sym.quot C n).left (Work.SymQuot.Sym C n).hom
      ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom) rfl hq_uc
  -- `q ≫ Δ_g = Δ_f ≫ (q ×_K q)`
  have hcomp := pullback.comp_diagonal (Work.SymQuot.Sym.quot C n).left (Work.SymQuot.Sym C n).hom
  -- hence `range Δ_g = (q ×_K q) '' range Δ_f`
  have hrange : Set.range ⇑(pullback.diagonal (Work.SymQuot.Sym C n).hom)
      = ⇑(pullback.map
          ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
          ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
          (Work.SymQuot.Sym C n).hom (Work.SymQuot.Sym C n).hom
          (Work.SymQuot.Sym.quot C n).left (Work.SymQuot.Sym.quot C n).left
          (𝟙 (Spec (CommRingCat.of K))) (by simp) (by simp)) ''
        Set.range ⇑(pullback.diagonal
          ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)) := by
    calc Set.range ⇑(pullback.diagonal (Work.SymQuot.Sym C n).hom)
        = Set.range (⇑(pullback.diagonal (Work.SymQuot.Sym C n).hom) ∘
            ⇑(Work.SymQuot.Sym.quot C n).left) := by
          rw [Set.range_comp]
          rw [show Set.range ⇑(Work.SymQuot.Sym.quot C n).left = Set.univ from
            Set.eq_univ_of_forall hsurj, Set.image_univ]
      _ = Set.range ⇑((Work.SymQuot.Sym.quot C n).left ≫
            pullback.diagonal (Work.SymQuot.Sym C n).hom) := rfl
      _ = Set.range ⇑(pullback.diagonal
            ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom) ≫
            pullback.map
              ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
              ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
              (Work.SymQuot.Sym C n).hom (Work.SymQuot.Sym C n).hom
              (Work.SymQuot.Sym.quot C n).left (Work.SymQuot.Sym.quot C n).left
              (𝟙 (Spec (CommRingCat.of K))) (by simp) (by simp)) := by rw [hcomp]
      _ = Set.range (⇑(pullback.map
              ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
              ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
              (Work.SymQuot.Sym C n).hom (Work.SymQuot.Sym C n).hom
              (Work.SymQuot.Sym.quot C n).left (Work.SymQuot.Sym.quot C n).left
              (𝟙 (Spec (CommRingCat.of K))) (by simp) (by simp)) ∘
            ⇑(pullback.diagonal
              ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom))) := rfl
      _ = ⇑(pullback.map
              ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
              ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)
              (Work.SymQuot.Sym C n).hom (Work.SymQuot.Sym C n).hom
              (Work.SymQuot.Sym.quot C n).left (Work.SymQuot.Sym.quot C n).left
              (𝟙 (Spec (CommRingCat.of K))) (by simp) (by simp)) ''
            Set.range ⇑(pullback.diagonal
              ((Work.SymQuot.Sym.quot C n).left ≫ (Work.SymQuot.Sym C n).hom)) :=
          Set.range_comp _ _
  -- the diagonal is an immersion with closed range, hence a closed immersion
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [hrange]
  exact hclosedqq _
    (hFsep.isClosedImmersion_diagonal.isClosedEmbedding.isClosed_range)

end Work.SymQuot.Sym
