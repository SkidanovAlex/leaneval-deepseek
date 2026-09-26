import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.thinCorner_distance_increasing

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ### Helpers for `Work.Drive.radialGapOfTools`

Two elementary facts about the metric of the parameter circle `AddCircle period`: a real number
lying between `ρ` and `period - ρ` is at circular distance at least `ρ` from `0`, and the circular
separation is symmetric.  Both are used to convert the "far" branch of the hypotheses `hgap` /
`hgapb` into a lower bound on `circSep`. -/

private lemma rg_norm_coe_ge {e ρ : ℝ} (hρ : 0 ≤ ρ) (he0 : 0 < e) (heP : e < period)
    (h1 : ρ ≤ e) (h2 : ρ ≤ period - e) : ρ ≤ ‖(e : AddCircle period)‖ := by
  have hP : 0 < period := period_pos
  rcases le_or_gt e (period / 2) with hle | hgt
  · have habs : |e| ≤ |period| / 2 := by
      rw [abs_of_pos he0, abs_of_pos hP]; linarith
    have := (AddCircle.norm_coe_eq_abs_iff period hP.ne').mpr habs
    rw [this, abs_of_pos he0]; exact h1
  · have hcoe : (e : AddCircle period) = ((e - period : ℝ) : AddCircle period) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    have hlt : e - period < 0 := by linarith
    have habs : |e - period| ≤ |period| / 2 := by
      rw [abs_of_neg hlt, abs_of_pos hP]; linarith
    have := (AddCircle.norm_coe_eq_abs_iff period hP.ne').mpr habs
    rw [hcoe, this, abs_of_neg hlt]
    linarith

/-- A lower bound for the circular separation: if `ρ ≤ u - x ≤ period - ρ` and `ρ > 0`, then the
classes of `u` and `x` are at distance at least `ρ` on the parameter circle. -/
private lemma rg_circSep_ge {x u ρ : ℝ} (hρ : 0 < ρ)
    (h1 : ρ ≤ u - x) (h2 : u - x ≤ period - ρ) : ρ ≤ circSep u x := by
  have he0 : 0 < u - x := lt_of_lt_of_le hρ h1
  have heP : u - x < period := by linarith
  have h := rg_norm_coe_ge hρ.le he0 heP h1 (by linarith)
  rw [circSep, dist_eq_norm, ← AddCircle.coe_sub]
  exact h

private lemma rg_circSep_comm (x y : ℝ) : circSep x y = circSep y x := by
  simp [circSep, dist_comm]

open LeanEval.KnotTheory.Quadrisecant in
/-- **The radial gap at the two cut points of the thin loop.**  From the two radial tools — the
distance-increasing property at the scale `ρ₀` (in both the `x ± ρ₀` forms, as supplied by
`Work.Drive.thinCornerDistanceIncreasingParam`) and the local monotonicity of the radial distance on
a window of length `δ ≥ 2 ρ₀` — the distance from `r a` to `r (a + ρ₀)` is strictly smaller than the
distance from `r a` to any other point of the retained arc `[a + ρ₀, b - ρ₀]`, and likewise at the
other end.  This is the input of `Work.Drive.thinLoop_injOn`'s `hsep_a`/`hsep_b` (the lead's `G`),
via `Work.Drive.norm_thinCombo_le`. -/
theorem radialGapOfTools {r : ℝ → Space} {ρ₀ δ : ℝ} (hρ : 0 < ρ₀) (hδ : 0 < δ)
    (h2δ : 2 * ρ₀ ≤ δ)
    (hmono : ∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ →
      ‖r (a + s) - r a‖ < ‖r (a + s') - r a‖)
    (hmonob : ∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ →
      ‖r (a - s) - r a‖ < ‖r (a - s') - r a‖)
    (hgap : ∀ x s : ℝ, 2 * ρ₀ ≤ circSep s x → ‖r (x + ρ₀) - r x‖ < ‖r s - r x‖)
    (hgapb : ∀ x s : ℝ, 2 * ρ₀ ≤ circSep s x → ‖r (x - ρ₀) - r x‖ < ‖r s - r x‖) :
    ∀ a b : ℝ, 0 < b - a → b - a ≤ period - 2 * ρ₀ →
      (∀ θ : ℝ, a + ρ₀ ≤ θ → θ ≤ b - ρ₀ → θ ≠ a + ρ₀ →
        ‖r (a + ρ₀) - r a‖ < ‖r θ - r a‖) ∧
      (∀ θ : ℝ, a + ρ₀ ≤ θ → θ ≤ b - ρ₀ → θ ≠ b - ρ₀ →
        ‖r (b - ρ₀) - r b‖ < ‖r θ - r b‖) := by
  intro a b hab hbL
  constructor
  · intro θ h1 h2 hne
    have hu_gt : ρ₀ < θ - a := by
      have hlt : a + ρ₀ < θ := lt_of_le_of_ne h1 (Ne.symm hne)
      linarith
    have hub : θ - a ≤ period - 2 * ρ₀ := by linarith
    rcases le_or_gt (θ - a) δ with hle | hgt
    · have hmon := hmono a ρ₀ (θ - a) hρ.le hu_gt hle
      have heq : a + (θ - a) = θ := by ring
      rw [heq] at hmon
      exact hmon
    · have h2ρ : 2 * ρ₀ < θ - a := lt_of_le_of_lt h2δ hgt
      have hsep : 2 * ρ₀ ≤ circSep θ a :=
        rg_circSep_ge (x := a) (u := θ) (ρ := 2 * ρ₀) (by linarith) (by linarith) hub
      exact hgap a θ hsep
  · intro θ h1 h2 hne
    have hv_gt : ρ₀ < b - θ := by
      have hlt : θ < b - ρ₀ := lt_of_le_of_ne h2 hne
      linarith
    have hvb : b - θ ≤ period - 2 * ρ₀ := by linarith
    rcases le_or_gt (b - θ) δ with hle | hgt
    · have hmon := hmonob b ρ₀ (b - θ) hρ.le hv_gt hle
      have heq : b - (b - θ) = θ := by ring
      rw [heq] at hmon
      exact hmon
    · have h2ρ : 2 * ρ₀ < b - θ := lt_of_le_of_lt h2δ hgt
      have hsep' : 2 * ρ₀ ≤ circSep b θ :=
        rg_circSep_ge (x := θ) (u := b) (ρ := 2 * ρ₀) (by linarith) (by linarith) hvb
      exact hgapb b θ (by rwa [rg_circSep_comm θ b])


end Work.Drive
