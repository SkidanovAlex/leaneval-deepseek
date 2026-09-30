import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit
import Submission.Work.DescentGeom.Transfer
import Submission.Work.DescentGeom.desc_mul
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.DescentGeom

open CategoryTheory Limits AlgebraicGeometry

open scoped CategoryTheory MonoidalCategory

universe u

theorem desc_AJ {k : Type u} [Field k] {C : Work.DescentGeom.Sch k}
    {P0 : 𝟙_ (Work.DescentGeom.Sch k) ⟶ C} (D : Work.DescentGeom.Input C P0) :
    ∃ AJ : C ⟶ D.J,
      (Work.DescentGeom.bcFun k D.k').map AJ = D.AJ' ≫ D.bcIso.inv := by
  -- The `k'`-morphism `C_{k'} ⟶ J` whose descent is the Abel–Jacobi map: the Abel–Jacobi map of
  -- the group chunk, transported to `J` along the descent isomorphism and projected to `J`.
  let Φ : (bc D.k' C).left ⟶ D.J.left := D.AJ'.left ≫ D.bcIso.inv.left ≫ bcπ D.k' D.J
  -- `Φ` is a morphism of `k`-schemes.
  have hΦ : Φ ≫ D.J.hom = (bc D.k' C).hom ≫ Work.Descent.specMap k D.k' := by
    have h1 : Φ = (D.AJ' ≫ D.bcIso.inv).left ≫ bcπ D.k' D.J := by
      dsimp only [Φ]
      rw [Over.comp_left (f := D.AJ') (g := D.bcIso.inv)]
      simp only [Category.assoc]
    rw [h1, Category.assoc, Work.Descent.baseChangeπ_hom, ← Category.assoc,
      Over.w (D.AJ' ≫ D.bcIso.inv)]
  -- `Φ` is `Γ`-invariant.
  have hInv : ∀ σ : Work.Descent.Gal k D.k', Work.Descent.galAct C σ ≫ Φ = Φ := by
    intro σ
    have hAJ : ∀ {T : Scheme.{u}} (X : D.G'.left ⟶ T),
        Work.Descent.galAct C σ ≫ D.AJ'.left ≫ X = D.AJ'.left ≫ (D.galAct σ).hom ≫ X := by
      intro T X
      rw [← Category.assoc, D.AJ'_compat σ, Category.assoc]
    have hb : ∀ {T : Scheme.{u}} (X : (bc D.k' D.J).left ⟶ T),
        (D.galAct σ).hom ≫ D.bcIso.inv.left ≫ X =
          D.bcIso.inv.left ≫ Work.Descent.galAct D.J σ ≫ X := by
      intro T X
      rw [← Category.assoc, DescMul.bcIso_inv_galAct D σ, Category.assoc]
    dsimp only [Φ]
    simp only [hAJ, hb, Work.Descent.galAct_π]
  -- Descent of `Φ` to a `k`-morphism `C ⟶ J`.
  obtain ⟨AJ, hAJ', -⟩ := desc_of_invariant C D.J Φ hΦ hInv
  refine ⟨AJ, ?_⟩
  have key : bcπ D.k' C ≫ AJ.left = (D.AJ' ≫ D.bcIso.inv).left ≫ bcπ D.k' D.J := by
    rw [hAJ']
    dsimp only [Φ]
    rw [Over.comp_left (f := D.AJ') (g := D.bcIso.inv)]
    simp only [Category.assoc]
  exact DescMul.map_eq_of_baseChange AJ (D.AJ' ≫ D.bcIso.inv) key

end Work.DescentGeom
