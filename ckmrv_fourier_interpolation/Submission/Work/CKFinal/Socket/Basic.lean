/-
# The socket region `U0` and the thinness scale for `Work.CKFinal.exists_F2_socket`

`Socket.U0` is the shared region `Work.CKFinal.U0` (the open strip `-1 < Re τ < 1` with the four
closed Farey discs of radius `1/4` centred at `±1/4`, `±3/4` removed), where the naive
`paperLayer` is holomorphic.  `Socket.thin` is the thinness scale `min(y²,1)/4` used to make the
window balls and the `Re τ = -1` strip thin enough.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.CKFinal.U0Defs

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- The thinness scale `min (y^2) 1 / 4`. -/
def thin (y : ℝ) : ℝ := min (y ^ 2) 1 / 4

/-- The socket region: the shared `Work.CKFinal.U0`. -/
abbrev U0 : Set ℍ := Work.CKFinal.U0

theorem isOpen_U0 : IsOpen U0 := Work.CKFinal.isOpen_U0

/-- From `‖z - c‖ > 1/2` and `‖p - c‖ ≤ 1/4` we get `‖z - p‖ > 1/4`. -/
lemma quarter_lt_norm_sub {z c p : ℂ} (h : 1 / 2 < ‖z - c‖) (hp : ‖p - c‖ ≤ 1 / 4) :
    1 / 4 < ‖z - p‖ := by
  have h1 : ‖z - c‖ ≤ ‖z - p‖ + ‖p - c‖ := by
    have h2 := norm_add_le (z - p) (p - c)
    rwa [show z - p + (p - c) = z - c by ring] at h2
  linarith [norm_nonneg (z - p)]

/-- `𝒟 ⊆ U0`: each of the four removed discs lies in one of the two lens regions
`|τ ∓ 1/2| ≤ 1/2`. -/
theorem DomainD_subset_U0 : Work.Asymptotics.DomainD ⊆ U0 := by
  intro τ hτ
  obtain ⟨hre1, hre2, hc1, hc2⟩ := hτ
  rw [Work.CKFinal.mem_U0_iff]
  have hc1' : 1 / 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ := hc1
  have hc2' : 1 / 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ := hc2
  refine ⟨hre1, hre2, ?_, ?_, ?_, ?_⟩
  · have h : ‖(1 / 4 : ℂ) - (1 / 2 : ℂ)‖ ≤ 1 / 4 := by norm_num
    have := quarter_lt_norm_sub hc1' h
    simpa using this
  · have h : ‖(-(1 / 4) : ℂ) - (-(1 / 2) : ℂ)‖ ≤ 1 / 4 := by norm_num
    have := quarter_lt_norm_sub (c := (-(1/2) : ℂ)) (z := (τ : ℂ)) (p := (-(1/4) : ℂ)) ?_ h
    · simpa using this
    · simpa [sub_eq_add_neg] using hc2'
  · have h : ‖(3 / 4 : ℂ) - (1 / 2 : ℂ)‖ ≤ 1 / 4 := by norm_num
    have := quarter_lt_norm_sub hc1' h
    simpa using this
  · have h : ‖(-(3 / 4) : ℂ) - (-(1 / 2) : ℂ)‖ ≤ 1 / 4 := by norm_num
    have := quarter_lt_norm_sub (c := (-(1/2) : ℂ)) (z := (τ : ℂ)) (p := (-(3/4) : ℂ)) ?_ h
    · simpa using this
    · simpa [sub_eq_add_neg] using hc2'

end Socket
end Work.CKFinal
