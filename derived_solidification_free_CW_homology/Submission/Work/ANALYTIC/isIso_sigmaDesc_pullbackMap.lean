import Mathlib
import Submission.Work.ANALYTIC.isUniversalColimit_colimitCocone_lightCondSet

/-!
# Pullbacks distribute over coproducts in `LightCondSet`

Small coproducts in `LightCondSet` are universal (stable under pullback), so for arbitrary index
types `ι`, `ι'` and families `X : ι → LightCondSet`, `Y : ι' → LightCondSet` with maps
`f i : X i ⟶ S`, `g j : Y j ⟶ S` into a common object `S` the canonical map

`∐_{i,j} (X i ×_S Y j) ⟶ (∐_i X i) ×_S (∐_j Y j)`

is an isomorphism.  This is the binary "distributivity" statement (in the fibre-product form
`pullback.map`), the `LightCondSet` analogue of `FinitaryPreExtensive.isIso_sigmaDesc_map` with
arbitrary index types.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

namespace Work.ANALYTIC

/-- The canonical coproduct cofan of a family in `LightCondSet` is a universal colimit. -/
theorem isUniversalColimit_cofan_lightCondSet {ι : Type} (X : ι → LightCondSet.{0})
    [HasCoproduct X] :
    IsUniversalColimit (Cofan.mk (∐ X) (Sigma.ι X)) := by
  refine IsUniversalColimit.of_iso
    (isUniversalColimit_colimitCocone_lightCondSet (F := Discrete.functor X)) (Cocone.ext ?_ ?_)
  · exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor X))
      (coproductIsCoproduct X)
  · intro j
    exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j

/-- **Pullbacks distribute over coproducts in `LightCondSet`.** -/
theorem isIso_sigmaDesc_pullbackMap_lightCondSet {ι ι' : Type} {S : LightCondSet.{0}}
    {X : ι → LightCondSet.{0}} {Y : ι' → LightCondSet.{0}}
    (f : ∀ i, X i ⟶ S) (g : ∀ j, Y j ⟶ S) [HasCoproduct X] [HasCoproduct Y]
    [HasCoproduct (fun p : ι × ι' => pullback (f p.1) (g p.2))] :
    IsIso (Sigma.desc (fun p : ι × ι' =>
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι X p.1) (Sigma.ι Y p.2)
        (𝟙 S) (by simp) (by simp))) := by
  let c : Cofan (fun p : ι × ι' => pullback (f p.1) (g p.2)) :=
    Cofan.mk _ <| fun p =>
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι X p.1) (Sigma.ι Y p.2)
        (𝟙 S) (by simp) (by simp)
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
    (a := Cofan.mk (∐ X) (Sigma.ι X)) (b := Cofan.mk (∐ Y) (Sigma.ι Y))
    (isUniversalColimit_cofan_lightCondSet X) (isUniversalColimit_cofan_lightCondSet Y)
    f g (Sigma.desc f) (Sigma.desc g) (fun i j => pullback.cone (f i) (g j))
    (fun i j => pullback.isLimit (f i) (g j)) (pullback.cone (Sigma.desc f) (Sigma.desc g))
    (pullback.isLimit _ _) (Iso.refl _)

end Work.ANALYTIC
