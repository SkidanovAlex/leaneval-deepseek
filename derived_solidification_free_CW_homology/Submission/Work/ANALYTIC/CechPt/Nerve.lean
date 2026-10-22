import Mathlib
import ChallengeDeps
import Submission.Work.ANALYTIC.CechPt.Setup

/-!
# The Čech nerve of a map of light condensed sets

For a map `β : X ⟶ Y` of light condensed sets (with `X` light profinite) we use Mathlib's
`Arrow.cechNerve` to get the Čech nerve of `β` as a simplicial object, and we record the
free-module simplicial object `p ↦ ℤ[X^•_Y]` whose alternating face complex is the Čech complex
`R` of `Submission/Work/ANALYTIC/NOTES_HI_pt.md`.
-/

open CategoryTheory Limits LightProfinite LightCondensed AlgebraicTopology

noncomputable section

namespace Work.ANALYTIC.CechPt

open _root_.LightCondensed

/-- The Čech nerve of a map of light condensed sets, as a simplicial object. -/
noncomputable def cechNerve {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) : SimplicialObject LightCondSet.{0} :=
  Arrow.cechNerve (Arrow.mk β)

/-- The free light condensed abelian group on the Čech nerve: the simplicial object
`p ↦ ℤ[X^•_Y]`. -/
noncomputable abbrev cechFree {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) : SimplicialObject LightCondAb :=
  cechNerve β ⋙ free ℤ

end Work.ANALYTIC.CechPt

namespace Work.ANALYTIC.CechPt

open _root_.LightCondensed

variable {X : LightProfinite.{0}} {Y : LightCondSet.{0}} (β : LightProfinite.toCondensed X ⟶ Y)

/-- The Čech complex of `β`, as a cochain complex of light condensed abelian groups concentrated
in degrees `≤ 0`: degree `-p` is `ℤ` on the `p`-th term of the Čech nerve. -/
noncomputable def cechComplex : CochainComplex LightCondAb ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor LightCondAb).obj
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (cechFree β))

/-- The augmentation of the Čech complex of `β`, in cochain form: `cechComplex β ⟶ ℤ[Y]`
concentrated in degree `0`. -/
noncomputable def cechAug : cechComplex β ⟶
    (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj ((free ℤ).obj Y) :=
  (ComplexShape.embeddingDownNat.extendFunctor LightCondAb).map
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        ((SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
          (Arrow.augmentedCechNerve (Arrow.mk β)))) ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat ((free ℤ).obj Y) 0 0
      (by simp)).hom

end Work.ANALYTIC.CechPt
