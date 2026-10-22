import Mathlib
import Submission.Work.ANALYTIC.CechPt.Setup
import Submission.Work.ANALYTIC.CechPt.Nerve
import Submission.Work.ANALYTIC.CechPt.Defs
import Submission.Work.ANALYTIC.CechPt.cech_h0
import Submission.Work.ANALYTIC.CechPt.cech_higher

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed AlgebraicTopology

noncomputable section

end

/-- **The Čech nerve of a cover is a resolution.**  For an epimorphism `β : X ⟶ Y` of light
condensed sets with `X` light profinite, the augmentation of the alternating-face complex of the
free-module Čech nerve `p ↦ ℤ[X ×_Y ⋯ ×_Y X]` (that is, `p ↦ ℤ[(Arrow.cechNerve β).obj p]`) is a
quasi-isomorphism onto `ℤ[Y]` concentrated in degree `0`.

Mathlib input: the case of a *split* epimorphism is
`Arrow.AugmentedCechNerve.extraDegeneracy` combined with
`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`; the general case should be obtained by
refining a test object to clopen pieces on which the pullback cover admits a section and gluing the
local extra degeneracies.  The intended application is `Y = [0,1]` (Hausdorff), `X` the Cantor set
and `β` the binary expansion; only that case is strictly needed.

The proof is split into degree `0` (`Work.ANALYTIC.CechPt.cech_h0`, which uses `Epi β`) and
positive degrees (`Work.ANALYTIC.CechPt.cech_higher`, which does not): the augmented Čech complex
of `ℤ[-]` applied to the Čech nerve is a resolution of `ℤ[Y]`. -/
theorem cech_descent {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) (hβ : Epi β) :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
        (Arrow.augmentedCechNerve (Arrow.mk β)))) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  match i with
  | 0 => exact cech_h0 β hβ
  | (n + 1) =>
      refine IsZero.isIso ?_ ?_ _
      · exact cech_higher β n
      · exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0
          ((free ℤ).obj Y) (n + 1) (Nat.succ_ne_zero n)

end Work.ANALYTIC.CechPt
