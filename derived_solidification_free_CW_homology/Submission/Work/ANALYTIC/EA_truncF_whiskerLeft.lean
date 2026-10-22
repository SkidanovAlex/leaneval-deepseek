import Mathlib
import Submission.Work.ANALYTIC.towerFEAsetup
import Submission.Work.ANALYTIC.exists_tower_F_EAdata
import Submission.Work.ANALYTIC.ihomPointsEval

namespace Work.ANALYTIC

open CategoryTheory MonoidalCategory

/-!
# The `EA`-form of the truncation data of `Work.ANALYTIC.truncF`, in whiskered form

`truncF : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ` is `MonoidalClosed.uncurry truncTheta`, so pushing it along a
generalized point `g : ℤ[S] ⟶ ∏^bnd ℤ` gives, by naturality of uncurrying, the uncurrying of
`g ≫ truncTheta`; by `Work.ANALYTIC.IhomPointsEval` this is the `S`-point of `truncTheta` at the
section classified by `g`, i.e. the descent `truncPsi S x` of `truncPhi S x` (with `x =
homFreeEquiv S boundedSeq g`).  Composing with `EA S` and using the characterizing property
`truncPsi_spec` of the descent closes the identity.

This is the whiskered form of `Work.ANALYTIC.IsTruncEAdata truncF` (`Work.ANALYTIC.truncPsi_spec`),
and reproduces `h3`/`h4` of `Work.ANALYTIC.comp_sBoundedZ_truncF`.
-/

/-- Pushing `truncF` along a generalized point `g` gives the descent `truncPsi` of the point `g`
itself, at the section `x = homFreeEquiv S boundedSeq g` classifying `g`. -/
theorem whiskerLeft_truncF (S : LightProfinite)
    (g : Work.ATOM.zfree S ⟶ Work.ANALYTIC.boundedSeq) :
    (LightCondensed.P ◁ g) ≫ Work.ANALYTIC.truncF
      = Work.ANALYTIC.truncPsi S (Work.ATOM.homFreeEquiv S Work.ANALYTIC.boundedSeq g) := by
  rw [Work.ANALYTIC.truncF, ← MonoidalClosed.uncurry_natural_left g Work.ANALYTIC.truncTheta]
  rw [← Work.ANALYTIC.ihomPointsEval LightCondensed.P Work.ANALYTIC.boundedSeq
    Work.ANALYTIC.boundedSeq Work.ANALYTIC.truncTheta S g]
  rw [Work.ANALYTIC.truncTheta_app]
  exact Equiv.apply_symm_apply _ _

/-- **The `EA`-form of the truncation data of `truncF`, in whiskered form.**  For `g : ℤ[S] ⟶
∏^bnd ℤ`, the composite `EA S ≫ (id_P ⊗ g) ≫ truncF` is the morphism
`ℤ[(ℕ∪{∞}) × S] ⟶ ∏^bnd ℤ` classified by `truncDataElem S x`, where `x = homFreeEquiv S
boundedSeq g` is the section of `∏^bnd ℤ` over `S` classified by `g`. -/
theorem EA_truncF_whiskerLeft (S : LightProfinite)
    (g : Work.ATOM.zfree S ⟶ Work.ANALYTIC.boundedSeq) :
    Work.ATOM.EA S ≫ (LightCondensed.P ◁ g) ≫ Work.ANALYTIC.truncF =
      Work.ANALYTIC.truncPhi S (Work.ATOM.homFreeEquiv S Work.ANALYTIC.boundedSeq g) := by
  rw [whiskerLeft_truncF S g, Work.ANALYTIC.truncPsi_spec]

end Work.ANALYTIC
