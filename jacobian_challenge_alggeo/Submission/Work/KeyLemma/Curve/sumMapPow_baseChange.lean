import Mathlib
import Submission.Work.KeyLemma.SymPow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory

namespace Work.KeyLemma.Curve

universe u
theorem sumMapPow_baseChange {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} {n : ℕ}
    (G : Work.KeyLemma.Curve.SymPow C n)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] (Φ : G.S ⟶ A) {L : Type u} [Field L] [Algebra k L]
    (bc : G.BaseChange L) (D : C.Div) (hD : D.IsEffective) (hn : C.deg D = (n : ℤ)) :
    Work.KeyLemma.Curve.sumMapPowBaseChange G Φ D hD hn =
      Work.KeyLemma.Curve.sumMapPowBC G Φ bc D hD hn := by
  unfold Work.KeyLemma.Curve.sumMapPowBaseChange Work.KeyLemma.Curve.sumMapPowBC
    Work.KeyLemma.Curve.sumMapPow
  rw [Work.KeyLemma.Curve.Pt.baseChange_comp]
  have hp : G.divOf (Classical.choose (G.divOf_complete D hD hn)) = D :=
    Classical.choose_spec (G.divOf_complete D hD hn)
  have hq : bc.G'.divOf (Classical.choose (bc.G'.divOf_complete (C.divMap L D)
      (bc.divMap_isEffective hD) ((bc.divMap_deg D).trans hn))) = C.divMap L D :=
    Classical.choose_spec (bc.G'.divOf_complete (C.divMap L D)
      (bc.divMap_isEffective hD) ((bc.divMap_deg D).trans hn))
  have key : (Work.KeyLemma.Curve.Pt.baseChange L (Classical.choose (G.divOf_complete D hD hn)) ≫
      bc.iso.hom) = Classical.choose (bc.G'.divOf_complete (C.divMap L D)
      (bc.divMap_isEffective hD) ((bc.divMap_deg D).trans hn)) :=
    bc.G'.divOf_injective (by rw [bc.divOf_iso, hp, hq])
  rw [← key]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end Work.KeyLemma.Curve
