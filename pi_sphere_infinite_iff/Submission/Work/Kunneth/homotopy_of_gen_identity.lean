import Mathlib
import Submission.Work.Kunneth.EzawWDefs
import Submission.Work.Kunneth.tChain_hom_ext

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

/-- The generator of the `(p,q)`-summand of the tensor complex `C_*(X) ⊗_ℤ C_*(Y)`, placed in
total degree `n` by means of a prescribed proof `hpq : p + q = n`.  For `n = p + q` and `hpq` the
canonical proof this is `genXY X Y σ τ`; the point of the definition is to have a *typed* element
of degree `n` available when `n` is an abstract natural number with `hpq : p + q = n` in hand. -/
noncomputable def genXYDeg (X Y : SSet) (n p q : ℕ) (hpq : p + q = n)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) : ↥((tChain X Y).X n) :=
  tpLof (sChain X) (sChain Y) n ⟨(p, q), hpq⟩ (genCh X σ ⊗ₜ[ℤ] genCh Y τ)

theorem homotopy_of_gen_identity (X Y : SSet)
    (W : (p q : ℕ) → ↥((Work.Kunneth.tMod p q).X (p + q + 1)))
    (hs : Work.Kunneth.HsumData X Y W)
    (hcomm : ∀ (p q : ℕ) (σ : X.obj (Opposite.op (SimplexCategory.mk p)))
      (τ : Y.obj (Opposite.op (SimplexCategory.mk q))),
      (Work.Kunneth.Ezaw X Y).f (p + q) (Work.Kunneth.genXY X Y σ τ)
        = ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
            ((Work.Kunneth.tChain X Y).d (p + q) (p + q - 1))
            (Work.Kunneth.homMap X Y W hs (p + q - 1) (p + q)))
            (Work.Kunneth.genXY X Y σ τ)
          + ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
              (Work.Kunneth.homMap X Y W hs (p + q) (p + q + 1))
              ((Work.Kunneth.tChain X Y).d (p + q + 1) (p + q)))
              (Work.Kunneth.genXY X Y σ τ)
          + Work.Kunneth.genXY X Y σ τ) :
    Nonempty (Homotopy (Work.Kunneth.Ezaw X Y)
      (CategoryTheory.CategoryStruct.id (Work.Kunneth.tChain X Y))) := by
  refine ⟨{ hom := homMap X Y W hs
            zero := fun i j hij => homMap_neg X Y W hs hij
            comm := fun i => ?_ }⟩
  have hdn : dNext i (homMap X Y W hs)
      = (tChain X Y).d i (i - 1) ≫ homMap X Y W hs (i - 1) i :=
    dNext_nat (tChain X Y) (tChain X Y) i _
  have hpd : prevD i (homMap X Y W hs)
      = homMap X Y W hs i (i + 1) ≫ (tChain X Y).d (i + 1) i :=
    prevD_eq (homMap X Y W hs) (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)
  have hcomm_gen : ∀ (n p q : ℕ) (hpq : p + q = n)
      (σ : X.obj (Opposite.op (SimplexCategory.mk p)))
      (τ : Y.obj (Opposite.op (SimplexCategory.mk q))),
      ModuleCat.Hom.hom ((Ezaw X Y).f n) (genXYDeg X Y n p q hpq σ τ)
        = ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
              ((tChain X Y).d n (n - 1)) (homMap X Y W hs (n - 1) n))
            (genXYDeg X Y n p q hpq σ τ)
          + ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
              (homMap X Y W hs n (n + 1)) ((tChain X Y).d (n + 1) n))
              (genXYDeg X Y n p q hpq σ τ)
          + genXYDeg X Y n p q hpq σ τ := by
    intro n p q hpq σ τ
    cases hpq
    exact hcomm p q σ τ
  rw [hdn, hpd]
  apply tChain_hom_ext
  intro p q hpq σ τ
  show ModuleCat.Hom.hom ((Ezaw X Y).f i) (genXYDeg X Y i p q hpq σ τ)
      = ModuleCat.Hom.hom ((tChain X Y).d i (i - 1) ≫ homMap X Y W hs (i - 1) i
          + homMap X Y W hs i (i + 1) ≫ (tChain X Y).d (i + 1) i
          + (CategoryTheory.CategoryStruct.id (tChain X Y)).f i)
        (genXYDeg X Y i p q hpq σ τ)
  rw [hcomm_gen i p q hpq σ τ]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]

end

end Work.Kunneth
