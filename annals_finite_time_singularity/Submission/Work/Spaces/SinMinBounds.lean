/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular endpoint bound `min θ (π/2 - θ) · sin(2θ)^{-b}`

For `0 ≤ b ≤ 1` the function `θ ↦ min θ (π/2 - θ) · sin(2θ)^{-b}` is bounded on
`Iθ = [0, π/2]`.  This is the elementary estimate which allows the angular weights
`sin(2θ)^{-η/2}`, `sin(2θ)^{-γ/2}` and `sin(2θ)^{-α/5}` to be controlled near the two
angular endpoints by the vanishing of the functions they multiply.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

#check @Real.rpow_le_one
#check @Real.mul_rpow
#check @Real.inv_rpow
#check @Real.rpow_add
#check @Real.rpow_le_rpow_of_nonpos
#check @Real.rpow_neg
#check @Real.mul_le_sin

theorem SinMinBounds (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ ∈ Iθ, min θ (π/2 - θ) * (Real.sin (2 * θ)) ^ (-b) ≤ K := by
  refine ⟨1, one_pos, fun θ hθ => ?_⟩
  have hπ := Real.pi_pos
  suffices key : ∀ s ∈ Iθ, s ≤ π / 4 → min s (π / 2 - s) * (Real.sin (2 * s)) ^ (-b) ≤ 1 by
    rcases le_total θ (π / 4) with h | h
    · exact key θ hθ h
    · have hs : π / 2 - θ ∈ Iθ := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
      have hsin : Real.sin (2 * (π / 2 - θ)) = Real.sin (2 * θ) := by
        rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]
      have hmin : min θ (π / 2 - θ) = min (π / 2 - θ) (π / 2 - (π / 2 - θ)) := by
        rw [show π / 2 - (π / 2 - θ) = θ by ring, min_comm]
      rw [hmin, ← hsin]
      exact key (π / 2 - θ) hs (by linarith)
  intro s hs hsle
  rw [min_eq_left (by linarith)]
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0]; simp
  have hsin0 : 0 ≤ Real.sin (2 * s) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hj : 4 / π * s ≤ Real.sin (2 * s) := by
    have h := Real.mul_le_sin (x := 2 * s) (by linarith) (by linarith)
    have h2 : 2 / π * (2 * s) = 4 / π * s := by ring
    linarith [h, h2]
  have h4s : 0 < 4 / π * s := by positivity
  have hstep1 : (Real.sin (2 * s)) ^ (-b) ≤ (4 / π * s) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos h4s hj (by linarith)
  have hstep2 : s * (4 / π * s) ^ (-b) ≤ 1 := by
    have e1 : (4 / π * s) ^ (-b) = (4 / π) ^ (-b) * s ^ (-b) :=
      Real.mul_rpow (z := -b) (by positivity) (le_of_lt h0)
    have e2 : (4 / π) ^ (-b) ≤ 1 := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / π),
        ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / π) b, inv_div]
      exact Real.rpow_le_one (by positivity) (by linarith [Real.pi_lt_four]) hb0
    have e3 : s * s ^ (-b) ≤ 1 := by
      rw [Real.rpow_neg (le_of_lt h0) b, ← div_eq_mul_inv,
        div_le_one (Real.rpow_pos_of_pos h0 b)]
      have h := Real.rpow_le_rpow_of_exponent_ge h0 (by linarith [Real.pi_lt_four]) hb1
      rwa [Real.rpow_one] at h
    rw [e1]
    have hle := mul_le_mul e2 e3 (le_of_lt (by positivity : (0 : ℝ) < s * s ^ (-b)))
      (by norm_num : (0 : ℝ) ≤ 1)
    have hre : s * ((4 / π) ^ (-b) * s ^ (-b)) = (4 / π) ^ (-b) * (s * s ^ (-b)) := by ring
    linarith [hre ▸ hle]
  have := mul_le_mul_of_nonneg_left hstep1 (le_of_lt h0)
  linarith [hstep2, this]

end Work.Spaces
