import Mathlib
import Submission.Work.OddCurve.LowSlope.AnchorRadialClose
import Submission.Work.OddEnvelope.Defs

/-!
# Radial gap bound for the low-slope odd reconstruction

If the cutting line at slope `s` meets the profile in a point of first coordinate
`r u * u` whose height is `r u * √(1 - u²)`, and that height is within `δ` of the
semicircle height `√(1 - (r u * u)²)`, then the radial factor `r u` is within `δ`
of `1`.

The analytic content is the purely two-dimensional fact that

  `|r - 1| ≤ |r * √(1 - u²) - √(1 - (r*u)²)|`  for `u ∈ (0,1)`, `r > 0`, `r*u ∈ (-1,1)`,

which is the reverse triangle inequality applied to the two points
`(r*u, r*√(1-u²))` (of norm `r`) and `(r*u, √(1-(r*u)²))` (of norm `1`):
they have the same first coordinate, so their distance is the difference of the
second coordinates, and it dominates the difference of the norms.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

/-- The planar reverse-triangle bound: for `u ∈ (0,1)`, `r > 0` with `r * u ∈ (-1,1)`,
the vertical gap between the point of the circle of radius `r` and the point of the unit
circle with the same first coordinate `r * u` dominates `|r - 1|`. -/
lemma radial_gap_core {u r : ℝ} (hu : 0 < u) (hu1 : u < 1) (hr : 0 < r)
    (ht : r * u ∈ Set.Ioo (-1 : ℝ) 1) :
    |r - 1| ≤ |r * Real.sqrt (1 - u ^ 2) - Real.sqrt (1 - (r * u) ^ 2)| := by
  have hu2 : u ^ 2 < 1 := by
    have h1 : |u| < 1 := abs_lt.mpr ⟨by linarith, hu1⟩
    nlinarith [abs_nonneg u, sq_abs u]
  have hru1 : r * u < 1 := ht.2
  have hru2 : (r * u) ^ 2 < 1 := by
    have h1 : |r * u| < 1 := abs_lt.mpr ht
    nlinarith [abs_nonneg (r * u), sq_abs (r * u)]
  have ha2 : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by linarith)
  have hc2 : Real.sqrt (1 - (r * u) ^ 2) ^ 2 = 1 - (r * u) ^ 2 := Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ Real.sqrt (1 - u ^ 2) := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt (1 - (r * u) ^ 2) := Real.sqrt_nonneg _
  have hone : 0 ≤ 1 - r * u ^ 2 := by
    have := mul_lt_mul_of_pos_right hru1 hu
    nlinarith
  have hsq : (Real.sqrt (1 - u ^ 2) * Real.sqrt (1 - (r * u) ^ 2)) ^ 2
      ≤ (1 - r * u ^ 2) ^ 2 := by
    rw [mul_pow, ha2, hc2]
    nlinarith [sq_nonneg (r - 1), sq_nonneg u, hu]
  have hac : Real.sqrt (1 - u ^ 2) * Real.sqrt (1 - (r * u) ^ 2) ≤ 1 - r * u ^ 2 := by
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (mul_nonneg ha0 hc0), abs_of_nonneg hone] at h
  have hkey : (r - 1) ^ 2
      ≤ (r * Real.sqrt (1 - u ^ 2) - Real.sqrt (1 - (r * u) ^ 2)) ^ 2 := by
    have h : 0 ≤ r * (1 - r * u ^ 2
        - Real.sqrt (1 - u ^ 2) * Real.sqrt (1 - (r * u) ^ 2)) :=
      mul_nonneg (le_of_lt hr) (by linarith)
    nlinarith [h, ha2, hc2]
  exact sq_le_sq.mp hkey

theorem radial_gap_bound {h X Y ρ : ℝ → ℝ} {u δ : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hρ : 0 < ρ u) (hρ0 : 0 ≤ ρ u)
    (ht : ρ u * u ∈ Set.Ioo (-1 : ℝ) 1)
    (hgraph : ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    (hf0 : 0 ≤ Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    (hf1 : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) ≤ 1)
    (hδ : 0 ≤ δ)
    (hclose : |Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)
      - Real.sqrt (1 - (ρ u * u) ^ 2)| ≤ δ) :
    |ρ u - 1| ≤ δ := by
  have hcore := radial_gap_core (u := u) (r := ρ u) hu hu1 hρ ht
  have hclose' : |ρ u * Real.sqrt (1 - u ^ 2) - Real.sqrt (1 - (ρ u * u) ^ 2)| ≤ δ := by
    simpa [← hgraph] using hclose
  linarith

end

end Work.OddCurve.LowSlope
