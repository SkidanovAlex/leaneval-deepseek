import Mathlib
import Submission.Work.Hormander.Weights.Rint
import Submission.Work.Hormander.Weights.rpair0_delta_left

/-!
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `rpair0_delta_right`

The right-hand counterpart of `rpair0_delta_left`:

`rpair0 φ X (∂_j Y - Y ∂_j φ) = -rpair0 φ (∂̄_j X) Y`.

Since the real pairing `rpair0` is symmetric (`rpair0_comm`), this is exactly
`rpair0_delta_left` applied to `(Y, X)` with the two arguments of `rpair0` swapped:

`rpair0 φ X (∂_j Y - Y ∂_j φ) = rpair0 φ (∂_j Y - Y ∂_j φ) X`
`  = -rpair0 φ Y (∂̄_j X) = -rpair0 φ (∂̄_j X) Y`.

Here `∂_j` is `dCoord n j` and `∂̄_j` is `dbarCoord n j`.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

theorem rpair0_delta_right {n : ℕ} (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) (j : Fin n)
    (X Y : Cn n → ℂ) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y)
    (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y) :
    rpair0 φ X (fun z => dCoord n j Y z - Y z * dPhi n j φ z)
      = -rpair0 φ (fun z => dbarCoord n j X z) Y := by
  rw [rpair0_comm (φ := φ) X (fun z => dCoord n j Y z - Y z * dPhi n j φ z)]
  rw [rpair0_delta_left φ hφ j Y X hY hX hsY hsX]
  rw [rpair0_comm (φ := φ) Y (fun z => dbarCoord n j X z)]

end Work.Hormander.Weights
