import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.K0_chordSurf_level

/-!
# B5: the level function of the chord chart at the chord parameter `r = π/2`

On the chord side `W τ t (r^2) = chordSurf CI.c a τ t r` (`hWchord`, `0 < r ≤ π/2`), and
`K₀ (chordSurf …) = r² ‖halfChord …‖² - 1`; at `r = π/2` this gives
`K₀ (W τ t (π²/4)) + 1 = ‖c(t+π/2) - c(t-π/2)‖²/4`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The chord-side level identity `r² ‖halfChord‖² = ‖z - w‖²/4` for `r ≠ 0`, i.e.
`r² ‖(z-w)/(2r)‖² = ‖z - w‖²/4` with `z = c τ (t+r)`, `w = c τ (t-r)`. -/
theorem halfChord_norm_sq (c : ℝ → ℝ → ℂ) (τ t r : ℝ) (hr : r ≠ 0) :
    r ^ 2 * ‖Work.RPB.halfChord c τ t r‖ ^ 2
      = ‖c τ (t + r) - c τ (t - r)‖ ^ 2 / 4 := by
  have hsq : ‖Work.RPB.halfChord c τ t r‖ ^ 2
      = ‖c τ (t + r) - c τ (t - r)‖ ^ 2 / (4 * r ^ 2) := by
    rw [Complex.sq_norm, Work.RPB.halfChord]
    rw [show (2 : ℂ) * ↑r = ((2 * r : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.sq_norm]
    rw [show (2 * r) * (2 * r) = 4 * r ^ 2 by ring_nf]
  rw [hsq]
  field_simp

/-- The level function of the chord chart at `ρ = π²/4`. -/
theorem chartLev_pi_div_four (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (hWchord : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0:ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0:ℝ) 1) (t : ℝ) :
    Work.RPV.K0 (W τ t (Real.pi^2/4)) + 1
      = ‖CI.c τ (t + Real.pi/2) - CI.c τ (t - Real.pi/2)‖^2 / 4 := by
  have hpi4 : Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 := by ring
  have hmem : Real.pi / 2 ∈ Set.Ioc (0:ℝ) (Real.pi / 2) :=
    ⟨by positivity, le_refl _⟩
  have hW := hWchord τ hτ t (Real.pi / 2) hmem
  rw [hpi4, hW, Work.RPB.B5.K0_chordSurf_level]
  exact halfChord_norm_sq CI.c τ t (Real.pi / 2)
    (ne_of_gt (by positivity : (0:ℝ) < Real.pi / 2))

end Work.RPB.B5
