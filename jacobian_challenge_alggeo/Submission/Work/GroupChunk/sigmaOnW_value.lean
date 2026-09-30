import Mathlib
import Submission.Work.GroupChunk.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.GroupChunk

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory
open scoped Work.GCBasics
open Work.GCBasics

universe u

noncomputable section

/-- **The value of a rational map computed by a partial map.**  If `p : Spec F ⟶ X` is a
point whose closed point lands in the domain of `σ : X ⤏ Y`, and `q` is a factorisation of
`p` through the domain of the partial map `σ.toPartialMap`, then the underlying morphism of
`value hred hsep σ hσ p hp` is `q.left ≫ σ.toPartialMap.hom`.

This unpacks the definition of `Work.GroupChunk.value`: the value is
`q₀.left ≫ σ.toPartialMap.hom` for the factorisation `q₀` produced by
`RPt.factor_of_closed_landsIn`, which is *unique*; any other factorisation `q` satisfies
`q = q₀` and hence gives the same morphism. -/
theorem value_left_eq {K : Type u} [Field K] {X Y : Sch K} (hred : IsReduced X.left)
    (hsep : IsSeparated Y.hom) (σ : X.left ⤏ Y.left)
    (hσ : σ.IsOver (Spec (CommRingCat.of K)))
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F)
    (hp : RPt.LandsIn p σ.domain)
    (q : RPt (Opens.toOver σ.domain) F)
    (hq : q ≫ Opens.ιOver σ.domain = p) :
    (value hred hsep σ hσ p hp).left = q.left ≫ σ.toPartialMap.hom := by
  haveI : IsReduced X.left := hred
  unfold value
  simp only [Over.homMk_left]
  congr 1
  have hdom : σ.toPartialMap.domain = σ.domain := rfl
  have hp' : RPt.LandsIn p σ.toPartialMap.domain := hdom.symm ▸ hp
  have hspec := Classical.choose_spec
    (RPt.factor_of_closed_landsIn (K := K) σ.toPartialMap.domain p hp')
  have huniq : Classical.choose
      (RPt.factor_of_closed_landsIn (K := K) σ.toPartialMap.domain p hp') = q :=
    (hspec.2 q (show q ≫ Opens.ιOver σ.toPartialMap.domain = p from hq)).symm
  rw [huniq]

theorem sigmaOnW_value {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt (Work.GCBasics.Opens.toOver (Work.GroupChunk.W i j)) F)
    (hp : Work.GCBasics.RPt.LandsIn (p ≫ Work.GCBasics.Opens.ιOver (Work.GroupChunk.W i j))
      (Work.GroupChunk.σ i j).domain) :
    p ≫ Work.GroupChunk.σOnW i j = Work.GroupChunk.σVal i j _ hp := by
  -- The inclusion of `W i j` into the domain of the partial map of `σ i j`.
  let g : Opens.toOver (W i j) ⟶ Opens.toOver (σ i j).domain :=
    Over.homMk (Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j)) (by
      change Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j) ≫
        (σPM i j).domain.ι ≫ (D.Sym D.g).hom = (W i j).ι ≫ (D.Sym D.g).hom
      rw [← Category.assoc, Scheme.homOfLE_ι])
  -- The factorisation of `p ≫ ιOver (W i j)` through the domain of `σ i j`.
  let q : RPt (Opens.toOver (σ i j).domain) F := p ≫ g
  have hgs : g ≫ Opens.ιOver (σ i j).domain = Opens.ιOver (W i j) := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Opens.ιOver_left]
    change Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j) ≫ (σPM i j).domain.ι = (W i j).ι
    rw [Scheme.homOfLE_ι]
  have hq : q ≫ Opens.ιOver (σ i j).domain = p ≫ Opens.ιOver (W i j) := by
    show p ≫ g ≫ Opens.ιOver (σ i j).domain = p ≫ Opens.ιOver (W i j)
    rw [hgs]
  have hval := value_left_eq (X := D.Sym D.g) (Y := D.Sym D.g) (hred := inferInstance)
    (hsep := inferInstance) (σ i j) (σ_isOver i j)
    (p ≫ Opens.ιOver (W i j)) hp q hq
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  rw [show (σOnW i j).left = Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j)
      ≫ (σ i j).toPartialMap.hom from rfl]
  rw [show (σVal i j (p ≫ Opens.ιOver (W i j)) hp).left =
      (value (inferInstance : IsReduced (D.Sym D.g).left)
      (inferInstance : IsSeparated (D.Sym D.g).hom) (σ i j) (σ_isOver i j)
      (p ≫ Opens.ιOver (W i j)) hp).left from rfl]
  rw [hval]
  show p.left ≫ (Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j) ≫ (σ i j).toPartialMap.hom)
    = (p.left ≫ Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j)) ≫ (σ i j).toPartialMap.hom
  rw [Category.assoc]

end

end Work.GroupChunk
