import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The one-variable Cauchy transform in the `m`-th coordinate, centred at `c m` and of
radius `2 * R`. -/
noncomputable def cauchyTransformCoord {n : ℕ} (m : Fin n) (c : Fin n → ℂ) (R : ℝ)
    (h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  cauchyTransform (2 * R) (fun w => h (Function.update z m (c m + w))) (z m - c m)

end Work.CR.Flat.Cauchy
