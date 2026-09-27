import Mathlib
import Submission.Work.KT.EG.kappa_lin_defs
import Submission.Work.KT.Fund.Kappa

namespace Work.KT.EG.KLG

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

/-- The constant function with value `t₀` on a space `Y`. -/
def cylConst {Y : Type} [TopologicalSpace Y] (t₀ : ℝ) : C(Y, ℂ) :=
  algebraMap ℂ C(Y, ℂ) ((t₀ : ℝ) : ℂ)

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The homotopy matrix `z • (a + (s t₀) b) + (s t₀) • a + b` over the cylinder `(X × I) × S¹`,
deforming the general linear clutching function `z • a + b` (`s = 0`) to the "reduced" linear
clutching function `z • (a + t₀ b) + (t₀ • a + b)` (`s = 1`).  Here `s` is the interval coordinate
and `z` the circle coordinate, and `t₀` is a real parameter. -/
def linBig {n : ℕ} (a b : Matrix (Fin n) (Fin n) C(X, ℂ)) (t₀ : ℝ) :
    Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ) :=
  (Work.KT.EG.zCyl X) • (Work.KT.EG.pullBig X a
      + ((Work.KT.EG.tCyl X) * (cylConst t₀ : C((X × unitInterval) × Sph ℂ, ℂ)))
        • Work.KT.EG.pullBig X b)
    + ((Work.KT.EG.tCyl X) * (cylConst t₀ : C((X × unitInterval) × Sph ℂ, ℂ)))
        • Work.KT.EG.pullBig X a
    + Work.KT.EG.pullBig X b

end

end Work.KT.EG.KLG
