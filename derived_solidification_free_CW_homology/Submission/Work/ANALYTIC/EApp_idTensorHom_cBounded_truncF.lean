import Mathlib
import Submission.Work.ANALYTIC.exists_tower_F_EAdata
import Submission.Work.ANALYTIC.BoundedSeqC
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ATOM.Defs
import Submission.Work.ANALYTIC.ihomPointsEval

/-!
# The truncation tower composed with the null sequence `c`

This file evaluates the composite

`EApp ≫ (id_P ⊗ c) ≫ truncF : ℤ[(ℕ∪∞) × (ℕ∪∞)] ⟶ ∏^bnd ℤ`

in terms of the truncation data of the null sequence `deltaElem = (δ_n)_n`:

`EApp ≫ (id_P ⊗ c) ≫ truncF = truncDataElem (ℕ∪∞) deltaElem`

(where the right hand side denotes the morphism classified by that section).

## The computation

Writing `EApp = EA (ℕ∪∞) ≫ (P ◁ P_proj)` (`Work.ATOM.EApp`, `Work.ATOM.EA`), using that tensor
products are functorial (`whiskerLeft_comp`), the defining property of `c = cBounded`
(`Work.ANALYTIC.P_proj_cBounded`: `P_proj ≫ c` is the morphism classified by `deltaElem`), the
naturality of uncurrying (`MonoidalClosed.uncurry_natural_left') and the evaluation formula for the
points of an internal hom (`Work.ANALYTIC.ihomPointsEval`, together with
`Work.ANALYTIC.truncTheta_app`), the composite becomes

`EA (ℕ∪∞) ≫ truncPsi (ℕ∪∞) deltaElem`,

which is `truncPhi (ℕ∪∞) deltaElem` by the characterizing identity of the descent
(`Work.ANALYTIC.truncPsi_spec`), and this is by definition the morphism classified by
`Work.ANALYTIC.truncDataElem (ℕ∪∞) deltaElem`.

Note `ℤ[(ℕ∪∞) × (ℕ∪∞)] = ℤ[NS2]` and `NS (ℕ∪∞) = NS2`, so the source of the composite and the
target of the classifying equivalence agree.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

-- needed to rewrite `P_proj ≫ cBounded` (`Work.ANALYTIC.freeHomEquiv`) against the
-- `Work.ATOM.homFreeEquiv`-flavoured statements used below; the two equivalences are
-- definitionally equal.
set_option backward.isDefEq.respectTransparency false

noncomputable section

theorem EApp_idTensorHom_cBounded_truncF : CategoryTheory.CategoryStruct.comp Work.ATOM.EApp (CategoryTheory.CategoryStruct.comp (Work.ATOM.idTensorHom Work.ANALYTIC.cBounded) Work.ANALYTIC.truncF) = (Work.ATOM.homFreeEquiv Work.ATOM.NS2 Work.ANALYTIC.boundedSeq).symm (Work.ANALYTIC.truncDataElem LightProfinite.NatUnionInfty Work.ANALYTIC.deltaElem) := by
  -- `EApp = EA (ℕ∪∞) ≫ (P ◁ P_proj)`
  have hEApp : Work.ATOM.EApp =
      Work.ATOM.EA LightProfinite.NatUnionInfty ≫ (LightCondensed.P ◁ LightCondensed.P_proj) := by
    simp only [Work.ATOM.EApp, Work.ATOM.EA, Category.assoc]
  -- `P_proj ≫ c` is the morphism classified by `deltaElem`
  have hg : (LightCondensed.P ◁ LightCondensed.P_proj) ≫ (LightCondensed.P ◁ Work.ANALYTIC.cBounded)
      = LightCondensed.P ◁
          ((Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq).symm
            Work.ANALYTIC.deltaElem) := by
    rw [← MonoidalCategory.whiskerLeft_comp]
    congr 1
    exact Work.ANALYTIC.P_proj_cBounded
  -- `(P ◁ g) ≫ truncF` is the uncurrying of `g ≫ truncTheta`
  have hT : (LightCondensed.P ◁
        ((Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq).symm
          Work.ANALYTIC.deltaElem)) ≫ Work.ANALYTIC.truncF
      = MonoidalClosed.uncurry
          (((Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq).symm
            Work.ANALYTIC.deltaElem) ≫ Work.ANALYTIC.truncTheta) := by
    rw [show Work.ANALYTIC.truncF = MonoidalClosed.uncurry Work.ANALYTIC.truncTheta from rfl]
    exact (MonoidalClosed.uncurry_natural_left _ _).symm
  -- evaluating the `S`-point of `truncTheta` at the section classified by `g` gives `truncPsi`
  have hu : MonoidalClosed.uncurry
        (((Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq).symm
          Work.ANALYTIC.deltaElem) ≫ Work.ANALYTIC.truncTheta)
      = Work.ANALYTIC.truncPsi LightProfinite.NatUnionInfty Work.ANALYTIC.deltaElem := by
    rw [← Work.ANALYTIC.ihomPointsEval LightCondensed.P Work.ANALYTIC.boundedSeq Work.ANALYTIC.boundedSeq
        Work.ANALYTIC.truncTheta LightProfinite.NatUnionInfty
        ((Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq).symm
          Work.ANALYTIC.deltaElem)]
    rw [show Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq
          ((Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq).symm
            (Work.ANALYTIC.deltaElem))
        = Work.ANALYTIC.deltaElem from Equiv.apply_symm_apply _ _]
    rw [Work.ANALYTIC.truncTheta_app]
    exact Equiv.apply_symm_apply _ _
  -- the characterizing identity of the descent, in the form of the truncation data
  have hp : Work.ATOM.EA LightProfinite.NatUnionInfty ≫
        Work.ANALYTIC.truncPsi LightProfinite.NatUnionInfty Work.ANALYTIC.deltaElem
      = (Work.ATOM.homFreeEquiv Work.ATOM.NS2 Work.ANALYTIC.boundedSeq).symm
          (Work.ANALYTIC.truncDataElem LightProfinite.NatUnionInfty Work.ANALYTIC.deltaElem) := by
    rw [Work.ANALYTIC.truncPsi_spec]
    rfl
  calc CategoryTheory.CategoryStruct.comp Work.ATOM.EApp (CategoryTheory.CategoryStruct.comp (Work.ATOM.idTensorHom Work.ANALYTIC.cBounded) Work.ANALYTIC.truncF)
      = Work.ATOM.EA LightProfinite.NatUnionInfty
          ≫ ((LightCondensed.P ◁ LightCondensed.P_proj)
              ≫ ((LightCondensed.P ◁ Work.ANALYTIC.cBounded) ≫ Work.ANALYTIC.truncF)) := by
        rw [hEApp]; simp only [Category.assoc]
    _ = Work.ATOM.EA LightProfinite.NatUnionInfty
          ≫ ((LightCondensed.P ◁
              ((Work.ATOM.homFreeEquiv LightProfinite.NatUnionInfty Work.ANALYTIC.boundedSeq).symm
                Work.ANALYTIC.deltaElem)) ≫ Work.ANALYTIC.truncF) := by
        rw [← Category.assoc (LightCondensed.P ◁ LightCondensed.P_proj)
            (LightCondensed.P ◁ Work.ANALYTIC.cBounded) Work.ANALYTIC.truncF, hg]
    _ = Work.ATOM.EA LightProfinite.NatUnionInfty ≫
          Work.ANALYTIC.truncPsi LightProfinite.NatUnionInfty Work.ANALYTIC.deltaElem := by
        rw [hT, hu]
    _ = _ := hp

end

end Work.ANALYTIC
