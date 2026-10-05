import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.V
import Submission.Work.RPB.B2.chordSurf_Tk_invariants
import Submission.Work.RPB.B2.chordSurf_inj_endgame

/-!
# B2: the chord annulus is injective onto its image, up to the `K₀`-flow

`Work.RPB.B2.chordSurf_injective`: on the strip `0 ≤ τ ≤ 1`, `t ∈ ℝ`, `0 < r < π` the map
`(t, r) ↦ chordSurf c a τ t r` is injective up to the `2π`-shift `Tk k` of the phase.  If two
points of the chord annulus agree up to `Tk k`, then the chord parameters agree on the nose
(`r' = r`) and differ only by a full period (`t' = t + 2πm`).

The argument (all coordinates are read off `PS = ℝ⁴`):

* the `q₂`-coordinate of `chordPS` is the phase itself and `Tk k` only adds `2πk` to it, so
  `a τ t' r' = a τ t r + 2πk` (`chordSurf_Tk_invariants`);
* the `uproj` coordinate (`p₁ + i q₁`) gives the reduced coordinate, whence the chord sums agree;
* the `K₀` coordinate gives `‖z - w‖²/4 - 1`, whence the chord lengths agree;
* hence `exp (I a τ t' r') = exp (I a τ t r)` and the two `IsChordPhase.arg` identities
  `chordVec = ‖chordVec‖ * exp (I a)` give `c τ (t'+r') - c τ (t'-r') = c τ (t+r) - c τ (t-r)`.
  Together with the equality of the sums, this pins down both endpoints;
* `CurveIsotopy.inj` turns the endpoint equalities into the congruences
  `t' + r' ≡ t + r` and `t' - r' ≡ t - r` (mod `2π`), whose difference gives `r' - r ∈ πℤ`;
  as `r, r' ∈ (0, π)` this forces `r' = r`, and then `t' ≡ t` (mod `2π`)
  (`chordSurf_inj_endgame`).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

theorem chordSurf_injective (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
      ∀ r' ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ t' (k : ℤ),
        Work.RPB.chordSurf CI.c a τ t' r' = Work.RPV.Tk k (Work.RPB.chordSurf CI.c a τ t r) →
          r' = r ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m := by
  intro τ hτ t r hr r' hr' t' k h
  -- the three coordinates of `PS` extracted from the hypothesis
  obtain ⟨hphase, hsum, hnorm⟩ :=
    Work.RPB.B2.chordSurf_Tk_invariants CI a τ hτ t r hr r' hr' t' k h
  -- the phase hypothesis `a τ t' r' = a τ t r + 2πk` makes the exponentials agree
  have hexp : Complex.exp (a τ t' r' * I) = Complex.exp (a τ t r * I) := by
    have harg : ((a τ t r + 2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * I
        = ((a τ t r : ℝ) : ℂ) * I + (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast
      ring
    rw [hphase, harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- `IsChordPhase.arg` for the two chords, with `chordVec` unfolded
  have hc' : CI.c τ (t' + r') - CI.c τ (t' - r')
      = (‖CI.c τ (t' + r') - CI.c τ (t' - r')‖ : ℂ) * Complex.exp (a τ t' r' * I) := by
    simpa only [Work.RPB.chordVec] using ha.2.1 τ hτ t' r' hr'
  have hc : CI.c τ (t + r) - CI.c τ (t - r)
      = (‖CI.c τ (t + r) - CI.c τ (t - r)‖ : ℂ) * Complex.exp (a τ t r * I) := by
    simpa only [Work.RPB.chordVec] using ha.2.1 τ hτ t r hr
  -- hence the chord vectors agree ...
  have hZ : CI.c τ (t' + r') - CI.c τ (t' - r') = CI.c τ (t + r) - CI.c τ (t - r) := by
    calc CI.c τ (t' + r') - CI.c τ (t' - r')
        = (‖CI.c τ (t' + r') - CI.c τ (t' - r')‖ : ℂ) * Complex.exp (a τ t' r' * I) := hc'
      _ = (‖CI.c τ (t + r) - CI.c τ (t - r)‖ : ℂ) * Complex.exp (a τ t r * I) := by
          rw [hnorm, hexp]
      _ = CI.c τ (t + r) - CI.c τ (t - r) := hc.symm
  -- ... and so do the two endpoints
  have hz : CI.c τ (t' + r') = CI.c τ (t + r) := by
    have h3 : CI.c τ (t' + r') + CI.c τ (t' - r') +
        (CI.c τ (t' + r') - CI.c τ (t' - r')) =
        CI.c τ (t + r) + CI.c τ (t - r) + (CI.c τ (t + r) - CI.c τ (t - r)) := by
      rw [hsum, hZ]
    have h4 : CI.c τ (t' + r') + CI.c τ (t' - r') +
        (CI.c τ (t' + r') - CI.c τ (t' - r')) = 2 * CI.c τ (t' + r') := by ring
    have h5 : CI.c τ (t + r) + CI.c τ (t - r) + (CI.c τ (t + r) - CI.c τ (t - r))
        = 2 * CI.c τ (t + r) := by ring
    rw [h4, h5] at h3
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h3
  have hw : CI.c τ (t' - r') = CI.c τ (t - r) := by
    have h3 : CI.c τ (t' + r') + CI.c τ (t' - r') -
        (CI.c τ (t' + r') - CI.c τ (t' - r')) =
        CI.c τ (t + r) + CI.c τ (t - r) - (CI.c τ (t + r) - CI.c τ (t - r)) := by
      rw [hsum, hZ]
    have h4 : CI.c τ (t' + r') + CI.c τ (t' - r') -
        (CI.c τ (t' + r') - CI.c τ (t' - r')) = 2 * CI.c τ (t' - r') := by ring
    have h5 : CI.c τ (t + r) + CI.c τ (t - r) - (CI.c τ (t + r) - CI.c τ (t - r))
        = 2 * CI.c τ (t - r) := by ring
    rw [h4, h5] at h3
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h3
  -- the topology of the curve turns these into congruences
  obtain ⟨m₁, hm₁⟩ := CI.inj τ hτ (t + r) (t' + r') hz.symm
  obtain ⟨m₂, hm₂⟩ := CI.inj τ hτ (t - r) (t' - r') hw.symm
  exact Work.RPB.B2.chordSurf_inj_endgame hr.1 hr.2 hr'.1 hr'.2 hm₁ hm₂

end Work.RPB.B2
