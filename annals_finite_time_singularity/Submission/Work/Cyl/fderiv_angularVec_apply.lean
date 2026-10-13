import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- `angularVec y = (-y₁, y₀, 0)` is the continuous linear map
`(proj 1).smulRight (-e₀) + (proj 0).smulRight e₁`, hence its Fréchet derivative at any point is
itself. -/
theorem fderiv_angularVec_apply (x v : Work.Cyl.R3) :
    fderiv ℝ (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) x v = Work.Cyl.angularVec v := by
  have hL : (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) =
      ⇑((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).smulRight (-Work.Cyl.e0)
        + (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).smulRight
            Work.Cyl.e1 : Work.Cyl.R3 →L[ℝ] Work.Cyl.R3) := by
    funext y
    refine Work.Cyl.ext_coord ?_ ?_ ?_ <;>
      simp [Work.Cyl.angularVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e,
        ContinuousLinearMap.smulRight_apply]
  rw [hL, ContinuousLinearMap.fderiv]
  exact (congrFun hL v).symm

end Work.Cyl
