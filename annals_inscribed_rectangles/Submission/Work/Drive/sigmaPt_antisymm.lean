import Mathlib
import Submission.Work.Drive.UmlaufSetup

namespace Work.Drive

/-- The direction of `-z` is the (complex) negation of the direction of `z`, for `z ≠ 0`:
`(-z)/‖-z‖ = -(z/‖z‖)`. -/
lemma dirOf_neg {z : ℂ} (hz : z ≠ 0) : dirOf (-z) = -(dirOf z) := by
  apply Subtype.ext
  rw [Circle.coe_neg, dirOf_coe (neg_ne_zero.mpr hz), dirOf_coe hz, norm_neg]
  ring

/-- The tangent direction of a `2π`-periodic curve with `2π`-periodic derivative is `2π`-periodic. -/
lemma tangDir_periodic {c : ℝ → ℝ × ℝ} (hc : RegCurve c) (t : ℝ) :
    tangDir c (t + 2 * Real.pi) = tangDir c t := by
  unfold tangDir
  rw [hc.deriv_periodic t]

/-- Hopf's secant map at the corner `(t₀, t₀)` is the tangent direction. -/
lemma sigmaPt_diag (c : ℝ → ℝ × ℝ) (t₀ : ℝ) :
    sigmaPt c t₀ (t₀, t₀) = tangDir c t₀ := by
  unfold sigmaPt
  rw [if_neg]
  · rw [if_neg (lt_irrefl t₀)]
  · rintro ⟨-, h⟩
    linarith [Real.pi_pos]

/-- Hopf's secant map at the far corner `(t₀, t₀+2π)` is the negated tangent direction. -/
lemma sigmaPt_far_diag (c : ℝ → ℝ × ℝ) (t₀ : ℝ) :
    sigmaPt c t₀ (t₀, t₀ + 2 * Real.pi) = -(tangDir c t₀) := by
  unfold sigmaPt
  rw [if_pos ⟨rfl, rfl⟩]

/-- Hopf's secant map at the last corner `(t₀+2π, t₀+2π)` is the tangent direction (at `t₀+2π`). -/
lemma sigmaPt_snd_corner (c : ℝ → ℝ × ℝ) (t₀ : ℝ) :
    sigmaPt c t₀ (t₀ + 2 * Real.pi, t₀ + 2 * Real.pi) = tangDir c (t₀ + 2 * Real.pi) := by
  unfold sigmaPt
  rw [if_neg]
  · rw [if_neg (lt_irrefl _)]
  · rintro ⟨h, -⟩
    linarith [Real.pi_pos]

/-- On the sloping side `s ↦ (s, t₀+2π)`, strictly inside the triangle, Hopf's map is the secant
direction from `s` to `t₀+2π`. -/
lemma sigmaPt_fst_edge (c : ℝ → ℝ × ℝ) {t₀ s : ℝ}
    (h1 : t₀ < s) (h2 : s < t₀ + 2 * Real.pi) :
    sigmaPt c t₀ (s, t₀ + 2 * Real.pi) = secDir c s (t₀ + 2 * Real.pi) := by
  unfold sigmaPt
  rw [if_neg, if_pos h2]
  rintro ⟨h, -⟩
  linarith

/-- On the sloping side `s ↦ (t₀, s)`, strictly inside the triangle, Hopf's map is the secant
direction from `t₀` to `s`. -/
lemma sigmaPt_snd_edge (c : ℝ → ℝ × ℝ) {t₀ s : ℝ}
    (h1 : t₀ < s) (h2 : s < t₀ + 2 * Real.pi) :
    sigmaPt c t₀ (t₀, s) = secDir c t₀ s := by
  unfold sigmaPt
  rw [if_neg, if_pos h1]
  rintro ⟨-, h⟩
  linarith

/-- Two parameters strictly inside an open period give distinct points of a regular closed curve. -/
lemma curve_ne_of_lt_of_lt {c : ℝ → ℝ × ℝ} (hc : RegCurve c) {a b : ℝ}
    (hab : a < b) (hba : b < a + 2 * Real.pi) : c a ≠ c b := by
  intro h
  obtain ⟨k, hk⟩ := (hc.eq_iff a b).mp h
  have hk0 : (k : ℝ) < 0 := by
    have : (k : ℝ) * (2 * Real.pi) = a - b := by linarith
    nlinarith [Real.pi_pos]
  have hkgt : (-1 : ℝ) < (k : ℝ) := by
    have : (k : ℝ) * (2 * Real.pi) = a - b := by linarith
    nlinarith [Real.pi_pos]
  have hk0' : k < 0 := by exact_mod_cast hk0
  have hkgt' : (-1 : ℤ) < k := by exact_mod_cast hkgt
  omega

/-- The two sloping sides of the triangle, strictly inside, have opposite secant directions. -/
lemma secDir_antisymm (c : ℝ → ℝ × ℝ) (hc : RegCurve c) {t₀ s : ℝ}
    (h1 : t₀ < s) (h2 : s < t₀ + 2 * Real.pi) :
    secDir c s (t₀ + 2 * Real.pi) = -(secDir c t₀ s) := by
  have hne : c s ≠ c t₀ := (curve_ne_of_lt_of_lt hc h1 h2).symm
  have hz : toC (c s - c t₀) ≠ 0 := by
    rw [toC_ne_zero_iff]
    exact sub_ne_zero.mpr hne
  unfold secDir
  rw [hc.periodic t₀]
  rw [← dirOf_neg hz, ← toC_neg, neg_sub]

/-- The two sloping sides of Hopf's triangle are traversed in opposite directions.

For `t₀ < s < t₀+2π` the secant from `c (t₀+2π) = c t₀` to `c s` is the negative of the secant
from `c t₀` to `c s`, so their directions are opposite; this also holds at the two endpoints,
where `sigmaPt` takes the tangent direction `±tangDir c t₀` (use `hc.deriv_periodic` for the
endpoint `t₀+2π`).  Unfold `sigmaPt` (each branch) and use
`Work.Drive.dirOf (toC (-v)) = -(Work.Drive.dirOf (toC v))` for `toC v ≠ 0`, plus `toC_neg` and
`hc.periodic`. -/
theorem sigmaPt_antisymm (c : ℝ → ℝ × ℝ) (hc : Work.Drive.RegCurve c) {t₀ : ℝ} {s : ℝ}
    (hs : s ∈ Set.Icc t₀ (t₀ + 2 * Real.pi)) :
    Work.Drive.sigmaPt c t₀ (s, t₀ + 2 * Real.pi) = -(Work.Drive.sigmaPt c t₀ (t₀, s)) := by
  obtain ⟨hs1, hs2⟩ := hs
  rcases lt_trichotomy s t₀ with hlt | heq | hgt
  · exact absurd hs1 (not_le.mpr hlt)
  · subst heq
    rw [sigmaPt_far_diag, sigmaPt_diag]
  · rcases lt_or_eq_of_le hs2 with hlt2 | heq2
    · rw [sigmaPt_fst_edge c hgt hlt2, sigmaPt_snd_edge c hgt hlt2]
      exact secDir_antisymm c hc hgt hlt2
    · subst heq2
      rw [sigmaPt_snd_corner, sigmaPt_far_diag, neg_neg, tangDir_periodic hc]

end Work.Drive
