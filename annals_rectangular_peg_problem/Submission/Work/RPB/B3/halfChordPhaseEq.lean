import Mathlib
import Submission.Work.RPB.Defs

namespace Work.RPB.B3

/-- Dividing a complex number by a positive *real* scalar preserves the phase: if `z` has phase
`a` (i.e. `z = ‖z‖ * exp (a * I)`), then so does `z / d` for `0 < d`.  The two sides of the
identity have literally the same phase factor, so this is where the statement of `halfChordPhaseEq`
comes from: `halfChord` is `chordVec` divided by the positive scalar `2r`. -/
lemma div_phase {z : ℂ} {d : ℝ} (hd : 0 < d) {a : ℝ}
    (h : z = (‖z‖ : ℂ) * Complex.exp (a * Complex.I)) :
    z / (d : ℂ) = (‖z / (d : ℂ)‖ : ℂ) * Complex.exp (a * Complex.I) := by
  have hnorm : ‖z / (d : ℂ)‖ = ‖z‖ / d := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le]
  rw [hnorm, Complex.ofReal_div]
  conv_lhs => rw [h]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem halfChordPhaseEq (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase c a) (hc' : ℝ → ℝ → ℝ → ℂ)
    (hc'_half : ∀ τ t r, r ≠ 0 → hc' τ t r = Work.RPB.halfChord c τ t r) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
      hc' τ t r = (‖hc' τ t r‖ : ℂ) * Complex.exp (a τ t r * Complex.I) := by
  intro τ hτ t r hr
  rw [hc'_half τ t r (ne_of_gt hr.1)]
  unfold Work.RPB.halfChord
  have h2 : ((2 : ℂ) * (r : ℂ)) = ((2 * r : ℝ) : ℂ) := by push_cast; ring
  rw [h2]
  exact div_phase (by linarith [hr.1]) (ha.2.1 τ hτ t r hr)

end Work.RPB.B3
