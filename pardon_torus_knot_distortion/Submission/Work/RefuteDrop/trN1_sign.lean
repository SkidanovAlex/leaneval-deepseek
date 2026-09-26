import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.dropTrace

/-!
# The sign of `trN1` on the two arcs where the trace meets the `y`-faces of the box

The function `trN1` of `RefuteDrop/dropTrace.lean` is the numerator of the first coordinate of
both branches of the trace of the cutting plane, and it is a pure trigonometric polynomial:
writing `c = cos u`, `s = sin u`,

`trN1 u = (7761/10000) * c + (4907/5000) * s`.

The `y`-window `|gammaA u 1| ≤ yclip` is therefore controlled by `|trN1 u|`.  This file
determines the sign of `trN1` on the two arcs of the `u`-interval that occur in the
definition of the points `yA1`, `yA2` in `dropTrace.lean`, namely

* `trN1 u > 0` for `u ∈ [0, ang (5/2)]`, and
* `trN1 u < 0` for `u ∈ [ang (9/2), π]`.

Both are proved by the same elementary observation.  Let `c = cos u`, `s = sin u` and
`M = (7761/10000, 4907/5000) = a (cos φ, sin φ)` with `tan φ = 4907/5000 * 10000/7761 = 9814/7761`.
The two endpoints of the first arc are the Pythagorean angles

* `u = 0`, where `(c, s) = (1, 0)`, and `trN1 = 7761/10000 > 0`,
* `u = ang (5/2)`, where `(c, s) = (-21/29, 20/29)`, and
  `trN1 = -(21/29) * 7761/10000 + (20/29) * 4907/5000 = 33299/290000 > 0`;

because `cos` is strictly antitone on `[0, π]`, the arc is contained in `c ∈ [-21/29, 1]`,
`s ≥ 0`, and on that range the linear function `a c + b s` is positive: where `c ≥ 0` this is
immediate, and where `c < 0` one has `c ≥ -21/29`, hence `s ≥ sqrt (1 - (21/29)^2) = 20/29`.
The second arc is analogous with the Pythagorean angle `ang (9/2)`, where
`(c, s) = (-77/85, 36/85)` and `trN1 = -(77/85) * 7761/10000 + (36/85) * 4907/5000
= -244293/850000 < 0`.
-/

namespace Work.RefuteDrop

open Work.BoxShrink.PinchOff.RefuteDrop

/-- `trN1` is the trigonometric polynomial `(7761/10000) cos u + (4907/5000) sin u`. -/
theorem trN1_eq_cos_sin (u : ℝ) :
    trN1 u = (7761/10000) * Real.cos u + (4907/5000) * Real.sin u := by
  simp only [trN1, trB1, trA]
  ring

/-- The value of `trN1` at the Pythagorean angle `ang (5/2)`, where
`cos = -21/29` and `sin = 20/29`. -/
theorem trN1_ang_five_halves : trN1 (ang (5/2)) = 33299/290000 := by
  rw [trN1_eq_cos_sin, cos_ang, sin_ang]
  norm_num

/-- The value of `trN1` at the Pythagorean angle `ang (9/2)`, where
`cos = -77/85` and `sin = 36/85`. -/
theorem trN1_ang_nine_halves : trN1 (ang (9/2)) = -244293/850000 := by
  rw [trN1_eq_cos_sin, cos_ang, sin_ang]
  norm_num

/-- **`trN1` is positive on the first arc** `[0, ang (5/2)]`. -/
theorem trN1_pos_of_le_ang_five_halves {u : ℝ} (hu1 : 0 ≤ u) (hu2 : u ≤ ang (5/2)) :
    0 < trN1 u := by
  have hpi : ang (5/2) < Real.pi := ang_lt_pi (by norm_num)
  -- the cosine is at least its value at the right endpoint `ang (5/2)`
  have hc : (-21/29 : ℝ) ≤ Real.cos u := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := u) (y := ang (5/2)) hu1
      (le_of_lt hpi) hu2
    rw [cos_ang] at h
    linarith [h]
  have hs : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu1 (le_trans hu2 (le_of_lt hpi))
  have hcs := Real.cos_sq_add_sin_sq u
  rw [trN1_eq_cos_sin]
  rcases le_or_gt 0 (Real.cos u) with hc0 | hc0
  · -- `c ≥ 0` and `s ≥ 0`: the sum is nonnegative, and it cannot vanish
    have hne : (7761/10000) * Real.cos u + (4907/5000) * Real.sin u ≠ 0 := by
      intro h
      have hz1 : Real.cos u = 0 := by nlinarith
      have hz2 : Real.sin u = 0 := by nlinarith
      nlinarith
    exact lt_of_le_of_ne (by nlinarith) (Ne.symm hne)
  · -- `c < 0`: then `c ≥ -21/29` forces `s ≥ 20/29`
    have hs20 : (20/29 : ℝ) ≤ Real.sin u := by
      nlinarith [hcs, hc, hs, hc0,
        mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ) ≤ Real.cos u + 21/29 by linarith)
          (le_of_lt hc0)]
    nlinarith [hc, hs20]

/-- **`trN1` is negative on the second arc** `[ang (9/2), π]`. -/
theorem trN1_neg_of_ang_nine_halves_le {u : ℝ} (hu1 : ang (9/2) ≤ u)
    (hu2 : u ≤ Real.pi) : trN1 u < 0 := by
  have hang : (0:ℝ) ≤ ang (9/2) := le_of_lt (ang_pos (by norm_num : (0:ℝ) < 9/2))
  have hu : (0:ℝ) ≤ u := le_trans hang hu1
  have hs : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu hu2
  have hcs := Real.cos_sq_add_sin_sq u
  -- the cosine is at most its value at the left endpoint `ang (9/2)`
  have hc : Real.cos u ≤ -77/85 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := ang (9/2)) (y := u) hang hu2 hu1
    rw [cos_ang] at h
    linarith [h]
  rw [trN1_eq_cos_sin]
  -- `c ≤ -77/85` forces `s ≤ sqrt (1 - (77/85)^2) = 36/85`
  have hs36 : Real.sin u ≤ 36/85 := by
    nlinarith [hcs, hc, hs, sq_nonneg (Real.cos u + 77/85)]
  nlinarith [hc, hs36]

/-- **The sign of `trN1` on the two arcs**: positive on `[0, ang (5/2)]` and negative on
`[ang (9/2), π]`. -/
theorem trN1_sign :
    (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (Work.BoxShrink.PinchOff.RefuteDrop.ang (5/2)) → 0 < Work.BoxShrink.PinchOff.RefuteDrop.trN1 u) ∧
    (∀ u : ℝ, u ∈ Set.Icc (Work.BoxShrink.PinchOff.RefuteDrop.ang (9/2)) Real.pi → Work.BoxShrink.PinchOff.RefuteDrop.trN1 u < 0) :=
  ⟨fun _u hu => trN1_pos_of_le_ang_five_halves hu.1 hu.2,
    fun _u hu => trN1_neg_of_ang_nine_halves_le hu.1 hu.2⟩

end Work.RefuteDrop
