import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPCore.GenFun.Basic

namespace Work.RPCore.GenFun

theorem fderiv_invMap (ψ : Work.RPV.PS → Work.RPV.PS) (hψ : ContDiff ℝ 3 ψ)
    (hnear : ∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ Work.RPV.PS‖ ≤ 1 / 4)
    (hbij : Function.Bijective (Work.RPCore.GenFun.gproj ψ)) (y : Work.RPV.PS) :
    fderiv ℝ (Work.RPCore.GenFun.invMap ψ) y =
      ↑((Work.RPCore.GenFun.dgequivLin (fderiv ℝ ψ (Work.RPCore.GenFun.invMap ψ y))
        (hnear (Work.RPCore.GenFun.invMap ψ y))).symm) := by
  -- Write `a = invMap ψ y` so that the point can be named throughout.
  set a : Work.RPV.PS := Work.RPCore.GenFun.invMap ψ y with ha
  -- `invMap ψ` is a two-sided inverse of `gproj ψ` because `gproj ψ` is bijective.
  have hga : Work.RPCore.GenFun.gproj ψ a = y := Function.rightInverse_invFun hbij.2 y
  have hleft : ∀ x, Work.RPCore.GenFun.invMap ψ (Work.RPCore.GenFun.gproj ψ x) = x :=
    fun x => Function.leftInverse_invFun hbij.1 x
  -- `gproj ψ` has the invertible strict derivative `dgequivLin (fderiv ψ a)` at `a`.
  have hstrict : HasStrictFDerivAt (Work.RPCore.GenFun.gproj ψ)
      ((Work.RPCore.GenFun.dgequivLin (fderiv ℝ ψ a) (hnear a) : Work.RPV.PS →L[ℝ] Work.RPV.PS))
      a := by
    have h1 : HasStrictFDerivAt (Work.RPCore.GenFun.gproj ψ)
        (fderiv ℝ (Work.RPCore.GenFun.gproj ψ) a) a :=
      ((Work.RPCore.GenFun.contDiff_gproj hψ).contDiffAt).hasStrictFDerivAt (by norm_num)
    have h2 : fderiv ℝ (Work.RPCore.GenFun.gproj ψ) a =
        ((Work.RPCore.GenFun.dgequivLin (fderiv ℝ ψ a) (hnear a) : Work.RPV.PS →L[ℝ] Work.RPV.PS)) := by
      rw [Work.RPCore.GenFun.fderiv_gproj ψ hψ a, Work.RPCore.GenFun.coe_dgequivLin]
    exact h1.congr_fderiv h2
  -- Hence the left inverse `invMap ψ` has derivative the inverse linear equivalence.
  have hfinal : HasStrictFDerivAt (Work.RPCore.GenFun.invMap ψ)
      ((Work.RPCore.GenFun.dgequivLin (fderiv ℝ ψ a) (hnear a)).symm : Work.RPV.PS →L[ℝ] Work.RPV.PS)
      (Work.RPCore.GenFun.gproj ψ a) :=
    hstrict.to_local_left_inverse (Filter.Eventually.of_forall hleft)
  rw [← hga]
  exact hfinal.hasFDerivAt.fderiv

end Work.RPCore.GenFun
