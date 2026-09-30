import Mathlib
import Submission.Work.Thom.CapGeomDefs

namespace Work.Thom.CapScale

/-- `Φ_λ v` is the unit vector with the same first `n` coordinates as `v` and last coordinate
`λ · lastC v`, normalised.  For `λ = 1` no normalisation happens: the defining vector
`scaleV n 1 v.1 = (strip v.1, 1 · lastC v.1)` is `v.1` itself. -/
theorem scalePt_one (n : ℕ) (v : MSph (n + 1)) (h : scaleV n 1 v.1 ≠ 0) :
    scalePt n 1 v h = v := by
  apply Subtype.ext
  rw [scalePt_val]
  have hv : scaleV n 1 v.1 = v.1 := by
    rw [scaleV, one_mul, lastC]
    exact Work.Morse.snocLp_strip v.1
  rw [hv, v.2, inv_one, one_smul]

end Work.Thom.CapScale
