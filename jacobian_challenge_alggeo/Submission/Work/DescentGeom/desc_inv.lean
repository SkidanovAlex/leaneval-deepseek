import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit
import Submission.Work.DescentGeom.Transfer
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

set_option linter.style.haveILetI false

namespace Work.DescentGeom

open CategoryTheory Limits

open scoped CategoryTheory MonObj MonoidalCategory

/-- The inverse law of the descended group chunk `J`: the inverse of the group object `G'` over
`k'` is `Γ`-equivariant (`D.galAct_inv_compat`), so conjugating it by the `Γ`-equivariant descent
isomorphism `bcIso : J_{k'} ≅ G'` produces a `Γ`-equivariant endomorphism of `J_{k'}`, which
descends to a `k`-endomorphism `inv` of `J` (via `desc_of_invariant`, applied to the neutral
`Galois-invariant` morphism `J_{k'} ⟶ J` obtained by projecting the endomorphism along `bcπ`).

The proof of the equivariance of the conjugated endomorphism is the categorical computation
`g_J (a ι a⁻¹) = (g_J a) ι a⁻¹ = a (g_G ι) a⁻¹ = a (ι g_G) a⁻¹ = a ι (g_G a⁻¹) = a ι a⁻¹ g_J`,
using `bcIso_compat` (equivariance of `a = bcIso.hom`), `galAct_inv_compat` (equivariance of `ι`)
and the equivariance of `a⁻¹ = bcIso.inv` derived from `bcIso_compat`. -/
theorem desc_inv {k : Type u} [Field k] {C : Work.DescentGeom.Sch k}
    {P0 : 𝟙_ (Work.DescentGeom.Sch k) ⟶ C} (D : Work.DescentGeom.Input C P0) :
    ∃ inv : D.J ⟶ D.J, (Work.DescentGeom.bcFun k D.k').map inv =
      D.bcIso.hom ≫ ι[D.G'] ≫ D.bcIso.inv := by
  haveI : FiniteDimensional k D.k' := D.finiteDimensional'
  haveI : IsGalois k D.k' := D.isGalois'
  -- The candidate endomorphism of `J_{k'}`, and the descent isomorphism as an isomorphism of
  -- underlying schemes.
  let Ψ : Work.DescentGeom.bc D.k' D.J ⟶ Work.DescentGeom.bc D.k' D.J :=
    D.bcIso.hom ≫ ι[D.G'] ≫ D.bcIso.inv
  let a : (Work.DescentGeom.bc D.k' D.J).left ≅ D.G'.left :=
    { hom := D.bcIso.hom.left
      inv := D.bcIso.inv.left
      hom_inv_id := by rw [← Over.comp_left, D.bcIso.hom_inv_id, Over.id_left]
      inv_hom_id := by rw [← Over.comp_left, D.bcIso.inv_hom_id, Over.id_left] }
  -- `bcIso.inv` is equivariant (the inverse of an equivariant isomorphism).
  have hbinv : ∀ σ, (D.galAct σ).hom ≫ a.inv = a.inv ≫ Work.Descent.galAct D.J σ := by
    intro σ
    have ha : Work.Descent.galAct D.J σ ≫ a.hom = a.hom ≫ (D.galAct σ).hom := D.bcIso_compat σ
    have h1 : a.inv ≫ Work.Descent.galAct D.J σ ≫ a.hom = (D.galAct σ).hom := by
      rw [ha, ← Category.assoc, a.inv_hom_id, Category.id_comp]
    rw [← h1, Category.assoc]
    simp only [Category.assoc]
    rw [a.hom_inv_id, Category.comp_id]
  -- Consequently `Ψ` is `Γ`-equivariant.
  have heq : ∀ σ, Work.Descent.galAct D.J σ ≫ Ψ.left = Ψ.left ≫ Work.Descent.galAct D.J σ := by
    intro σ
    have haa : Work.Descent.galAct D.J σ ≫ a.hom = a.hom ≫ (D.galAct σ).hom := D.bcIso_compat σ
    have hi : (D.galAct σ).hom ≫ (ι[D.G']).left = (ι[D.G']).left ≫ (D.galAct σ).hom :=
      D.galAct_inv_compat σ
    have hbb := hbinv σ
    simp only [Ψ, Over.comp_left]
    change Work.Descent.galAct D.J σ ≫ (a.hom ≫ (ι[D.G']).left ≫ a.inv) =
      (a.hom ≫ (ι[D.G']).left ≫ a.inv) ≫ Work.Descent.galAct D.J σ
    calc Work.Descent.galAct D.J σ ≫ (a.hom ≫ (ι[D.G']).left ≫ a.inv)
        = (Work.Descent.galAct D.J σ ≫ a.hom) ≫ ((ι[D.G']).left ≫ a.inv) := by
          rw [Category.assoc]
      _ = (a.hom ≫ (D.galAct σ).hom) ≫ ((ι[D.G']).left ≫ a.inv) := by rw [haa]
      _ = a.hom ≫ ((D.galAct σ).hom ≫ (ι[D.G']).left) ≫ a.inv := by simp only [Category.assoc]
      _ = a.hom ≫ ((ι[D.G']).left ≫ (D.galAct σ).hom) ≫ a.inv := by rw [hi]
      _ = a.hom ≫ (ι[D.G']).left ≫ ((D.galAct σ).hom ≫ a.inv) := by simp only [Category.assoc]
      _ = a.hom ≫ (ι[D.G']).left ≫ (a.inv ≫ Work.Descent.galAct D.J σ) := by rw [hbb]
      _ = (a.hom ≫ (ι[D.G']).left ≫ a.inv) ≫ Work.Descent.galAct D.J σ := by
          simp only [Category.assoc]
  -- The projected morphism `J_{k'} ⟶ J` is semilinear and `Γ`-invariant, so it descends.
  have hΦ : (Ψ.left ≫ Work.DescentGeom.bcπ D.k' D.J) ≫ D.J.hom =
      (Work.DescentGeom.bc D.k' D.J).hom ≫ Work.Descent.specMap k D.k' := by
    rw [Category.assoc, Work.Descent.baseChangeπ_hom D.J, ← Category.assoc, Over.w Ψ]
  have hΦinv : ∀ σ : Work.Descent.Gal k D.k',
      Work.Descent.galAct D.J σ ≫ (Ψ.left ≫ Work.DescentGeom.bcπ D.k' D.J) =
        Ψ.left ≫ Work.DescentGeom.bcπ D.k' D.J := by
    intro σ
    rw [← Category.assoc, heq σ, Category.assoc, Work.Descent.galAct_π D.J σ]
  obtain ⟨inv, hinv, -⟩ := Work.DescentGeom.desc_of_invariant (k := k) (k' := D.k')
    D.J D.J (Ψ.left ≫ Work.DescentGeom.bcπ D.k' D.J) hΦ hΦinv
  refine ⟨inv, ?_⟩
  -- `bcFun.map inv` and `Ψ` agree against both projections of the pullback `J_{k'}`.
  apply Over.OverMorphism.ext
  apply pullback.hom_ext (f := D.J.hom) (g := Work.Descent.specMap k D.k')
  · have hinv' : pullback.fst D.J.hom (Work.Descent.specMap k D.k') ≫ Over.Hom.left inv
        = Over.Hom.left Ψ ≫ pullback.fst D.J.hom (Work.Descent.specMap k D.k') := hinv
    rw [Work.Descent.baseChange_map_fst' (f := inv), hinv']
  · have hw1 : Over.Hom.left ((Work.DescentGeom.bcFun k D.k').map inv) ≫
        pullback.snd D.J.hom (Work.Descent.specMap k D.k') =
        pullback.snd D.J.hom (Work.Descent.specMap k D.k') :=
      Over.w ((Work.DescentGeom.bcFun k D.k').map inv)
    have hw2 : Over.Hom.left Ψ ≫ pullback.snd D.J.hom (Work.Descent.specMap k D.k') =
        pullback.snd D.J.hom (Work.Descent.specMap k D.k') := Over.w Ψ
    rw [hw1, hw2]

end Work.DescentGeom
