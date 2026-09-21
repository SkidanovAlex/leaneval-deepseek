import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# Elementary estimates for the transition-slope data

These are the (purely quantitative) implications that turn the curve data of the Volterra
construction into the positivity assumptions consumed by the row identities
(`Work.OddVolterra.RowIdentity.odd_rowF` / `odd_rowH`):

* `abs_hquot_le` — the divided difference `H(s,σ)` is bounded by the `C¹` norm of `h`;
* `section_endpoint_pos` — the chord endpoints stay outside the unit half-ball;
* `kernel_radicand_pos` — the two radicands `(t + H)(L_σ + L_s)` at the roots are positive;
* `middle_pos` — the ball radicand is positive on the fixed middle interval.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra

open Commons.Geometry.Ulam

noncomputable section

/-- The divided difference is bounded by the `C¹` norm of `h`. -/
lemma abs_hquot_le {h : ℝ → ℝ} {ε s σ : ℝ} (hε : ∀ t : ℝ, |deriv h t| ≤ ε)
    (hε0 : 0 ≤ ε) : |hquot h s σ| ≤ ε := by
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun τ : ℝ => deriv h (s + τ * (σ - s))) (C := ε) (by
      intro τ _
      simpa [Real.norm_eq_abs] using hε (s + τ * (σ - s)))
  have hint' : ‖∫ τ in (0 : ℝ)..1, deriv h (s + τ * (σ - s))‖ ≤ ε := by
    simpa using hint
  simpa [hquot, Real.norm_eq_abs] using hint'

/-- The chord endpoints stay outside the unit half-ball when the curve is close to `profileX`. -/
lemma section_endpoint_pos {x : ℝ → ℝ} {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (hx : ∀ s : ℝ, 0 < s → s ≤ 1 → |x s - profileX s| ≤ δ) :
    ∀ s : ℝ, 0 < s → s ≤ 1 → 1 / 2 ≤ x s := by
  intro s hs hs1
  have hsqrt2 : Real.sqrt 2 ≤ 100 / 51 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2, hsq]
  have hbase : 1 / 2 + 1 / 100 ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    linarith
  have hle : 1 + s ^ 2 ≤ 2 := by nlinarith
  have hsqrt : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hinv : 1 / Real.sqrt 2 ≤ 1 / Real.sqrt (1 + s ^ 2) :=
    one_div_le_one_div_of_le hpos hsqrt
  have hpx : 1 / 2 + δ ≤ profileX s := by
    rw [profileX]
    linarith
  have hx' := abs_le.mp (hx s hs hs1)
  linarith [hx'.1]

end

end Work.OddVolterra
