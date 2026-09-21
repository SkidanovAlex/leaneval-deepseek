import Mathlib

namespace Work.OddEnvelope.NonDegenerate

/-- If `f` is concave on `[a,b]`, with `f a = -(s*a+hs) < 0` and `f b = s*b+hs > 0`, then on the
open interval `(a,b)` the concave graph of `f` lies strictly outside the two lines `±(s*x+hs)`:
`(s*t+hs)^2 < (f t)^2`.

Geometrically: the chord of the concave function joining `(a, -L a)` to `(b, L b)` lies strictly
above `L t` and strictly above `-L t` for `a < t < b`, where `L x = s*x+hs`; and `f t` is above its
chord. -/
theorem sq_gt_sq_of_concaveOn_of_ends {f : ℝ → ℝ} {a b s hs : ℝ} (hab : a < b)
    (hf : ConcaveOn ℝ (Set.Icc a b) f)
    (ha : f a = -(s * a + hs)) (hb : f b = s * b + hs)
    (ha_neg : s * a + hs < 0) (hb_pos : 0 < s * b + hs) :
    ∀ t ∈ Set.Ioo a b, (s * t + hs) ^ 2 < (f t) ^ 2 := by
  intro t ht
  obtain ⟨hat, htb⟩ := ht
  have hba : 0 < b - a := by linarith
  have hta : 0 < t - a := by linarith
  have hbt : 0 < b - t := by linarith
  have hLa : 0 < -(s * a + hs) := by linarith
  have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab.le, le_refl b⟩
  have hqa : 0 ≤ (b - t) / (b - a) := by positivity
  have hra : 0 ≤ (t - a) / (b - a) := by positivity
  have hqr : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by
    field_simp
    ring
  have hcombo : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by
    field_simp
    ring
  -- concavity: `f t` is above the chord through `(a, f a)` and `(b, f b)`
  have hchord := hf.2 ha_mem hb_mem hqa hra hqr
  simp only [smul_eq_mul, hcombo] at hchord
  rw [ha, hb] at hchord
  -- chord minus the line `s*x+hs` is positive
  have h1 : 0 < f t - (s * t + hs) := by
    have hkey : 0 < (b - t) / (b - a) * (-(s * a + hs)) + (t - a) / (b - a) * (s * b + hs)
        - (s * t + hs) := by
      have he : (b - t) / (b - a) * (-(s * a + hs)) + (t - a) / (b - a) * (s * b + hs)
          - (s * t + hs) = 2 * (b - t) / (b - a) * (-(s * a + hs)) := by
        field_simp
        ring
      rw [he]
      have h2bt : 0 < 2 * (b - t) := by linarith
      exact mul_pos (div_pos h2bt hba) hLa
    linarith
  -- chord plus the line `s*x+hs` is positive
  have h2 : 0 < f t + (s * t + hs) := by
    have hkey : 0 < (b - t) / (b - a) * (-(s * a + hs)) + (t - a) / (b - a) * (s * b + hs)
        + (s * t + hs) := by
      have he : (b - t) / (b - a) * (-(s * a + hs)) + (t - a) / (b - a) * (s * b + hs)
          + (s * t + hs) = 2 * (t - a) / (b - a) * (s * b + hs) := by
        field_simp
        ring
      rw [he]
      have h2ta : 0 < 2 * (t - a) := by linarith
      exact mul_pos (div_pos h2ta hba) hb_pos
    linarith
  have hp : 0 < (f t - (s * t + hs)) * (f t + (s * t + hs)) := mul_pos h1 h2
  have he2 : (f t) ^ 2 - (s * t + hs) ^ 2 = (f t - (s * t + hs)) * (f t + (s * t + hs)) := by
    ring
  have hpos : 0 < (f t) ^ 2 - (s * t + hs) ^ 2 := by rw [he2]; exact hp
  linarith

end Work.OddEnvelope.NonDegenerate
