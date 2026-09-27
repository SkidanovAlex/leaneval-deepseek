import Mathlib
import Submission.Work.EQ.cayley_homeomorph_uhp

/-!
# The Cayley transform as a map into the upper half plane

`Work.EQ.cayleyUHP` is the Cayley transform `w ↦ i (1 + w) / (1 - w)` regarded as a map into the
upper half plane.  It is the natural `ℂ → ℍ` map underlying the disc cover of a component of `H0`:
for `‖w‖ < 1` it is the inverse of the `ℍ → 𝔻` Cayley homeomorphism, while off the disc it is
defined arbitrarily (so that it is a total function on `ℂ`).
-/

noncomputable section

open scoped Manifold
open Complex Metric

namespace Work.EQ

/-- The Cayley transform `w ↦ i (1 + w) / (1 - w)` as a map into the upper half plane, extended
arbitrarily outside the unit disc.  For `‖w‖ < 1` its underlying complex number is
`Work.EQ.cayley w`. -/
def cayleyUHP (w : ℂ) : UpperHalfPlane :=
  if hw : 0 < (cayley w).im then ⟨cayley w, hw⟩ else ⟨Complex.I, by simp⟩

/-- On the unit disc, `cayleyUHP` is the Cayley transform. -/
theorem cayleyUHP_coe {w : ℂ} (hw : ‖w‖ < 1) : (cayleyUHP w : ℂ) = cayley w := by
  rw [cayleyUHP, dite_eq_left (cayley_im_pos hw)]

/-- On the unit disc, `cayleyUHP` is the point of the upper half plane attached to `cayley w`. -/
theorem cayleyUHP_eq {w : ℂ} (hw : ‖w‖ < 1) :
    cayleyUHP w = ⟨cayley w, cayley_im_pos hw⟩ := by
  rw [cayleyUHP, dite_eq_left (cayley_im_pos hw)]

end Work.EQ
