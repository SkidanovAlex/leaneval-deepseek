import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit
import Submission.Work.DescentGeom.Transfer
import Submission.Work.DescentGeom.galActProdMap_naturality
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.DescentGeom

open CategoryTheory

open scoped CategoryTheory MonObj MonoidalCategory

open CartesianMonoidalCategory

universe u

/-! ### Auxiliary lemmas for the descent of the multiplication

These are kept in a separate namespace so that no name clashes with the other files of area
`DescentGeom` arise. -/

namespace DescMul

open CategoryTheory Limits

variable {k : Type u} [Field k]

/-- **A morphism of `k`-schemes whose base change agrees with a given `k'`-morphism on the
projection is that base change.**  If `φ : X ⟶ Y` is a morphism of `k`-schemes and
`Ψ : X_{k'} ⟶ Y_{k'}` is a morphism of `k'`-schemes whose underlying morphism satisfies
`bcπ ≫ φ = Ψ ≫ bcπ`, then `Ψ = φ_{k'}`.

Indeed a morphism into the fibre product `Y_{k'} = Y ×_{Spec k} Spec k'` is determined by its two
projections: against `bcπ` this is the hypothesis, and against the structure morphism it is
automatic because both `Ψ` and `φ_{k'}` are `k'`-morphisms. -/
theorem map_eq_of_baseChange {k' : Type u} [Field k'] [Algebra k k'] {X Y : Sch k}
    (φ : X ⟶ Y) (Ψ : bc k' X ⟶ bc k' Y)
    (h : bcπ k' X ≫ φ.left = Ψ.left ≫ bcπ k' Y) : (bcFun k k').map φ = Ψ := by
  apply Over.OverMorphism.ext
  refine pullback.hom_ext ?_ ?_
  · rw [Work.Descent.baseChange_map_fst']
    exact h
  · change Over.Hom.left ((bcFun k k').map φ) ≫ Over.hom (bc k' Y) =
      Over.Hom.left Ψ ≫ Over.hom (bc k' Y)
    rw [Over.w, Over.w]

variable {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C}

/-- The `k'`-morphism `(J ⊗ J)_{k'} ⟶ J_{k'}` obtained from the multiplication of the group chunk
`G'` and the descent isomorphism `J_{k'} ≅ G'`: this is the morphism whose descent is the
multiplication of the Jacobian `J`. -/
noncomputable def mulPhi (D : Input C P0) : bc D.k' (D.J ⊗ D.J) ⟶ bc D.k' D.J :=
  (CartesianMonoidalCategory.prodComparisonIso (bcFun k D.k') D.J D.J).hom ≫
    (D.bcIso.hom ⊗ₘ D.bcIso.hom) ≫ μ[D.G'] ≫ D.bcIso.inv

/-- The descent isomorphism `J_{k'} ≅ G'` is equivariant for the Galois action also in the
inverse direction: conjugating by `D.bcIso` turns the action on `G'` into the action on `J_{k'}`. -/
theorem bcIso_inv_galAct (D : Input C P0) (σ : Work.Descent.Gal k D.k') :
    (D.galAct σ).hom ≫ D.bcIso.inv.left =
      D.bcIso.inv.left ≫ Work.Descent.galAct D.J σ := by
  have h := D.bcIso_compat σ
  have h1 : D.bcIso.hom.left ≫ D.bcIso.inv.left = 𝟙 (bc D.k' D.J).left := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have h2 : D.bcIso.inv.left ≫ D.bcIso.hom.left = 𝟙 D.G'.left := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hL : (D.galAct σ).hom ≫ D.bcIso.inv.left =
      (((D.galAct σ).hom ≫ D.bcIso.inv.left) ≫ D.bcIso.hom.left) ≫ D.bcIso.inv.left := by
    rw [Category.assoc, h1, Category.comp_id]
  have hR : D.bcIso.inv.left ≫ Work.Descent.galAct D.J σ =
      ((D.bcIso.inv.left ≫ Work.Descent.galAct D.J σ) ≫ D.bcIso.hom.left) ≫
        D.bcIso.inv.left := by
    rw [Category.assoc, h1, Category.comp_id]
  have rG : ((D.galAct σ).hom ≫ D.bcIso.inv.left) ≫ D.bcIso.hom.left = (D.galAct σ).hom := by
    rw [Category.assoc, h2, Category.comp_id]
  have rI : ((D.bcIso.inv.left ≫ Work.Descent.galAct D.J σ) ≫ D.bcIso.hom.left) =
      (D.galAct σ).hom := by
    rw [Category.assoc, h, ← Category.assoc, h2, Category.id_comp]
  rw [hL, hR, rG, rI]

/-- **The morphism `mulPhi` is Galois-equivariant**: it is a morphism of descent data, hence
descends to a `k`-morphism `J ⊗ J ⟶ J`.

This is the compatibility of the multiplication `μ[G']` of the group chunk with the Galois action,
transported along the descent isomorphism, together with the naturality of the twisted diagonal
action `galActProdMap` on a product. -/
theorem mulPhi_galAct (D : Input C P0) (σ : Work.Descent.Gal k D.k') :
    Work.Descent.galAct (D.J ⊗ D.J) σ ≫ (mulPhi D).left =
      (mulPhi D).left ≫ Work.Descent.galAct D.J σ := by
  simp only [mulPhi, Over.comp_left]
  slice_lhs 1 2 => rw [galAct_prodComparison D.J D.J σ]
  slice_lhs 2 3 =>
    rw [galActProdMap_naturality D.bcIso.hom D.bcIso.hom (galActK D.k' D.J)
      (fun σ => (D.galAct σ).hom) (galActK D.k' D.J) (fun σ => (D.galAct σ).hom)
      (galActK_hom D.J) D.galAct_hom (galActK_hom D.J) D.galAct_hom D.bcIso_compat
      D.bcIso_compat σ]
  slice_lhs 3 4 =>
    rw [show galActProdMap D.G' D.G' (fun σ => (D.galAct σ).hom) (fun σ => (D.galAct σ).hom)
          D.galAct_hom D.galAct_hom σ ≫ μ[D.G'].left = μ[D.G'].left ≫ (D.galAct σ).hom from
        D.galAct_mul_compat σ]
  slice_lhs 4 5 => rw [bcIso_inv_galAct D σ]
  simp only [Category.assoc]

end DescMul

open scoped CategoryTheory MonObj MonoidalCategory

theorem desc_mul {k : Type u} [Field k] {C : Work.DescentGeom.Sch k}
    {P0 : 𝟙_ (Work.DescentGeom.Sch k) ⟶ C} (D : Work.DescentGeom.Input C P0) :
    ∃ mul : D.J ⊗ D.J ⟶ D.J,
      (Work.DescentGeom.bcFun k D.k').map mul =
        (CartesianMonoidalCategory.prodComparisonIso (Work.DescentGeom.bcFun k D.k') D.J D.J).hom ≫
          (D.bcIso.hom ⊗ₘ D.bcIso.hom) ≫ μ[D.G'] ≫ D.bcIso.inv := by
  -- The `Γ`-invariant `k`-morphism `(J ⊗ J)_{k'} ⟶ J` whose descent is the multiplication.
  let Φ : (bc D.k' (D.J ⊗ D.J)).left ⟶ D.J.left := (DescMul.mulPhi D).left ≫ bcπ D.k' D.J
  have hΦ : Φ ≫ D.J.hom = (bc D.k' (D.J ⊗ D.J)).hom ≫ Work.Descent.specMap k D.k' := by
    dsimp only [Φ]
    rw [Category.assoc, Work.Descent.baseChangeπ_hom, ← Category.assoc,
      Over.w (DescMul.mulPhi D)]
  have hInv : ∀ σ : Work.Descent.Gal k D.k',
      Work.Descent.galAct (D.J ⊗ D.J) σ ≫ Φ = Φ := by
    intro σ
    dsimp only [Φ]
    rw [← Category.assoc, DescMul.mulPhi_galAct, Category.assoc, Work.Descent.galAct_π]
  obtain ⟨mul, hmul, -⟩ := desc_of_invariant (D.J ⊗ D.J) D.J Φ hΦ hInv
  refine ⟨mul, ?_⟩
  have key : (bcFun k D.k').map mul = DescMul.mulPhi D :=
    DescMul.map_eq_of_baseChange mul (DescMul.mulPhi D) (by rw [hmul])
  rw [key]
  rfl

end Work.DescentGeom
