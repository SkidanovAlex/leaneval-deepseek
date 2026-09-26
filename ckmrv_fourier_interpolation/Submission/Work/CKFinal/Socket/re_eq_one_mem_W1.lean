/-
# The line `Re τ = 1` lies in `W1`

For `τ ∈ ℍ` with `Re τ = 1` the point `τ` is the *centre* `1 + i Im τ` of one of the window
balls, hence lies in `W1`.  This is the elementary geometric input of the socket construction
used by `Socket.closure_subset_O` (the closure of `𝒟` reaches the whole line `Re τ = 1`).
-/
import Mathlib
import Submission.Work.CKFinal.Socket.WinDefs

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- A point with `Re τ = 1` lies in `W1`: it is the centre of the window ball at height
`Im τ`. -/
lemma re_eq_one_mem_W1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (h : τ.re = 1) : τ ∈ W1 ℓ d hd := by
  refine mem_W1.mpr ⟨τ.im, τ.im_pos, ?_⟩
  have hτ : τ = Work.Asymptotics.onePlusI τ.im τ.im_pos := by
    apply UpperHalfPlane.ext
    rw [Work.Asymptotics.onePlusI_coe, ← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, h]
    norm_num
  have hpos : 0 < winRad ℓ d hd τ.im τ.im_pos := by
    unfold winRad winR
    exact lt_min (chartEps_pos ℓ d hd _ _) (by positivity)
  have hmem : Work.Asymptotics.onePlusI τ.im τ.im_pos ∈ winBall ℓ d hd τ.im τ.im_pos := by
    rw [winBall]
    exact Metric.mem_ball_self hpos
  rwa [← hτ] at hmem

end Socket
end Work.CKFinal
