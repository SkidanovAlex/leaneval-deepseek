/-
# The line `Re τ = -1` lies in `Wm1`

For `τ ∈ ℍ` with `Re τ = -1` the point `τ` lies in the region `Wm1`:

* `τ + 1` lies on the imaginary axis, hence in `U0` (the imaginary axis is at strict distance
  `> 1/4` from the four Farey disc centres `±1/4`, `±3/4`, because `Im τ > 0`);
* `τ + 2` has `Re = 1`, hence lies in `W1` (it is the centre of a window ball);
* and `|Re τ + 1| = 0 < thin (Im τ)`.

This is the elementary geometric input of the socket construction used by
`Work.CKFinal.Socket.F2_agree_Wm1` (the layer `F₂` is defined through one step of the recurrence
on the whole line `Re τ = -1`).
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Region
import Submission.Work.CKFinal.Socket.re_eq_one_mem_W1

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- Points of the imaginary axis `Re z = 0` lie at distance `> 1/4` from every real point `a`
with `|a| ≥ 1/4`: writing `z = i y` with `y > 0`, `‖z - a‖² = a² + y² > a² ≥ 1/16`. -/
lemma quarter_lt_norm_sub_of_re_eq_zero (z : ℍ) (hz : z.re = 0) (a : ℝ)
    (ha : (1 / 4 : ℝ) ≤ |a|) : (1 / 4 : ℝ) < ‖(z : ℂ) - (a : ℂ)‖ := by
  have hz' : (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    simpa using (Complex.re_add_im (z : ℂ)).symm
  have hsq : ‖(z : ℂ) - (a : ℂ)‖ ^ 2 = a ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hz', hz]
    simp
    ring
  have hain : (1 / 4 : ℝ) ^ 2 ≤ a ^ 2 := by
    have := sq_abs a
    rw [← this]
    exact pow_le_pow_left₀ (by norm_num) ha 2
  have him : 0 < z.im ^ 2 := by positivity
  have hnn : (0 : ℝ) ≤ ‖(z : ℂ) - (a : ℂ)‖ := norm_nonneg _
  nlinarith [hsq, him, hnn, hain]

/-- The imaginary axis `Re z = 0` lies in `U0`. -/
lemma imAxis_mem_U0 {z : ℍ} (hz : z.re = 0) : z ∈ U0 := by
  rw [Work.CKFinal.mem_U0_iff]
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · simpa using quarter_lt_norm_sub_of_re_eq_zero z hz (1 / 4) (by norm_num)
  · have h : (z : ℂ) + (1 / 4 : ℂ) = (z : ℂ) - ((-(1 / 4) : ℝ) : ℂ) := by norm_num
    rw [h]
    simpa using quarter_lt_norm_sub_of_re_eq_zero z hz (-(1 / 4)) (by norm_num)
  · simpa using quarter_lt_norm_sub_of_re_eq_zero z hz (3 / 4) (by norm_num)
  · have h : (z : ℂ) + (3 / 4 : ℂ) = (z : ℂ) - ((-(3 / 4) : ℝ) : ℂ) := by norm_num
    rw [h]
    simpa using quarter_lt_norm_sub_of_re_eq_zero z hz (-(3 / 4)) (by norm_num)

/-- A point with `Re τ = -1` lies in `Wm1`. -/
lemma re_eq_neg_one_mem_Wm1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (h : τ.re = -1) : τ ∈ Work.CKFinal.Socket.Wm1 ℓ d hd := by
  rw [mem_Wm1]
  have h1 : ((1 : ℝ) +ᵥ τ).re = 0 := by rw [vadd_one_re, h]; norm_num
  have h2 : ((2 : ℝ) +ᵥ τ).re = 1 := by rw [vadd_two_re, h]; norm_num
  refine ⟨imAxis_mem_U0 h1, re_eq_one_mem_W1 ℓ d hd _ h2, ?_⟩
  rw [h]
  simpa using thin_pos τ.im_pos

end Socket
end Work.CKFinal
