import Mathlib
import Submission.Work.Drive.thetaS_props
import Submission.Work.Drive.encodedShear

/-!
# Non-degeneracy of the level twist in its parameter, at a prescribed value

`Work.Drive.thetaS s x = x + clamp1 s * hb x` is the twist of the level interval of the shear
family (`encodedShear.lean`), with `clamp1 s = s / (2 √(1+s²))` the clamped parameter.  The
parameter direction is non-degenerate *everywhere* (`Work.Drive.thetaS_props`): for every `x` with
`hb x ≠ 0`, `d/ds θ_s x ≠ 0` at every `s`.

Here we record the form in which the consumer uses it: if the *value* `θ_r v` lies strictly inside
the interval, then the point `v` is not one of the two ends `0`, `1`, hence `hb v ≠ 0`, and the
derivative in the parameter direction does not vanish.  No hypothesis on `v` itself is needed: the
equation alone rules out the two degenerate values (`θ_r 0 = 0`, `θ_r 1 = 1` for every `r`).
-/

namespace Work.Drive

noncomputable section

/-- `θ_r` fixes both ends of the interval, for every parameter `r`. -/
@[simp] lemma thetaS_zero_right (r : ℝ) : thetaS r 0 = 0 := by simp [thetaS, hb]

/-- `θ_r 1 = 1` for every parameter `r` (the clamping makes the second factor collapse). -/
@[simp] lemma thetaS_one_right (r : ℝ) : thetaS r 1 = 1 := by simp [thetaS, hb]

/-- A point `v` whose image under the twist is not an end of the interval is not an end either, so
the bump `hb` does not vanish at it. -/
lemma hb_ne_zero_of_thetaS_eq (v r c₀ : ℝ) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1)
    (h : thetaS r v = c₀) : hb v ≠ 0 := by
  intro hz
  rw [hb] at hz
  rcases mul_eq_zero.mp hz with h' | h'
  · rw [h', thetaS_zero_right] at h
    linarith
  · rw [show v = 1 by linarith, thetaS_one_right] at h
    linarith

theorem deriv_thetaS_ne_zero_of_eq (v r c₀ : ℝ) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1)
    (h : Work.Drive.thetaS r v = c₀) :
    deriv (fun r' : ℝ => Work.Drive.thetaS r' v) r ≠ 0 :=
  (thetaS_props r).2.2 v r (hb_ne_zero_of_thetaS_eq v r c₀ hc₀0 hc₀1 h)

end

end Work.Drive
