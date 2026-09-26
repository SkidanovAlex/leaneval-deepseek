import ChallengeDeps

/-!
# Basic API for Pardon's distortion bound

This file contains the elementary reduction steps which turn the target inequality
`(1/160) * min p q ≤ distortion K` into the existence of an explicit pair of
parameters `s ≠ t` in the fundamental interval with a large distortion ratio.

The main point is that `distortion` is an `sSup` over `ℝ≥0∞`, a complete lattice,
so `le_sSup` applies *without* any boundedness hypothesis on the indexing set.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Submission

/-- Every distortion ratio at a pair of distinct parameters of the fundamental
interval is bounded by the distortion. -/
theorem le_distortion_of_pair (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t) :
    ENNReal.ofReal (distortionRatio K s t) ≤ distortion K :=
  le_sSup ⟨s, hs, t, ht, hst, rfl⟩

/-- To prove a lower bound for the distortion it suffices to exhibit a pair of
distinct parameters whose distortion ratio is at least that bound. -/
theorem le_distortion_of_pair' (K : Knot) {c : ℝ≥0∞} {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t)
    (h : c ≤ ENNReal.ofReal (distortionRatio K s t)) : c ≤ distortion K :=
  le_trans h (le_distortion_of_pair K hs ht hst)

/-- `(1/160 : ℝ≥0∞)` is the `ofReal` version of the real number `1/160`. -/
theorem coe_160 : (1 / 160 : ℝ≥0∞) = ENNReal.ofReal ((1 / 160 : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (y := 160) (by norm_num : (0 : ℝ) < 160), ENNReal.ofReal_one]
  norm_num

/-- `(1/160 : ℝ≥0∞) * n` for a natural number `n` is the `ofReal` version of the
corresponding real product. -/
theorem coe_160_mul (n : ℕ) :
    (1 / 160 : ℝ≥0∞) * (n : ℝ≥0∞) = ENNReal.ofReal ((1 / 160 : ℝ) * (n : ℝ)) := by
  rw [coe_160, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity)]

/-- Version of the reduction specialised to the target inequality of the
challenge: a single pair of parameters with ratio at least `min p q / 160`
suffices. -/
theorem target_of_pair (p q : ℕ) (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (hst : s ≠ t)
    (h : (1 / 160 : ℝ) * (Nat.min p q : ℝ) ≤ distortionRatio K s t) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K := by
  refine le_distortion_of_pair' K hs ht hst ?_
  rw [coe_160_mul (Nat.min p q)]
  exact ENNReal.ofReal_le_ofReal h

/-- The set of distortion ratios is nonempty: the distortion of any knot is at
least the ratio at the pair `(0, π)`. -/
theorem distortion_ge_ratio_zero_pi (K : Knot) :
    ENNReal.ofReal (distortionRatio K 0 Real.pi) ≤ distortion K := by
  refine le_distortion_of_pair K ?_ ?_ ?_
  · exact ⟨le_refl 0, by linarith [Real.pi_pos]⟩
  · exact ⟨le_of_lt Real.pi_pos, by linarith [Real.pi_pos]⟩
  · exact ne_of_lt (by linarith [Real.pi_pos])

end Submission
