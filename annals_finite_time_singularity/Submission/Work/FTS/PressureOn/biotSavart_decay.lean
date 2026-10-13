import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.LWP.BiotSavart.farField_decay_const
import Submission.Work.LWP.BiotSavart.nearField_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **Decay of the Biot–Savart field of a bounded, compactly supported vorticity.**
For `g` bounded by `M ≥ 0` and supported in the closed ball of radius `R`, the Newtonian-potential
Biot–Savart field decays like `(1 + ‖x‖²)⁻¹` at infinity:

  `∃ C ≥ 0, ∀ x, ‖biotSavart g x‖ ≤ C / (1 + ‖x‖²)`.

The proof glues the two unconditional Biot–Savart estimates:
`Work.LWP.BiotSavart.norm_biotSavart_near` (`‖x‖ ≤ 2R` gives the uniform bound `3 M R`) and
`Work.LWP.BiotSavart.farField_decay_const` (`2R ≤ ‖x‖` gives `(4/3) M R³ / ‖x‖²`).
Since the statement does not assume `0 ≤ R`, the radius is first replaced by `max R 0` — this only
enlarges the support, so both estimates still apply, and for `R < 0` the ball `closedBall 0 R` is
empty and the estimate degenerates to `0`. -/
theorem biotSavart_decay {g : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ y, ‖g y‖ ≤ M) (hsupp : ∀ y, g y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, ‖Work.LWP.biotSavart g x‖ ≤ C / (1 + ‖x‖ ^ 2) := by
  -- Step 0: replace the radius `R` by `R' = max R 0 ≥ 0`; this only enlarges the support.
  set R' : ℝ := max R 0 with hR'def
  have hR' : 0 ≤ R' := le_max_right R 0
  have hRR' : R ≤ R' := le_max_left R 0
  have hsupp' : ∀ y, g y ≠ 0 → y ∈ Metric.closedBall (0 : R3) R' :=
    fun y hy => Metric.closedBall_subset_closedBall hRR' (hsupp y hy)
  refine ⟨3 * M * R' * (1 + 4 * R' ^ 2), ?_, ?_⟩
  · -- nonnegativity of the constant
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hR')
      (by positivity)
  · intro x
    have hden : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
    rcases lt_or_ge (2 * R') ‖x‖ with hx | hx
    · -- **far field**: `2R' ≤ ‖x‖`, where the field decays like `‖x‖⁻²`
      have hx' : 2 * R' ≤ ‖x‖ := le_of_lt hx
      have hn : (0 : ℝ) < ‖x‖ := by linarith
      have hb := Work.LWP.BiotSavart.farField_decay_const hR' hM hg hsupp' x hx'
      refine hb.trans ?_
      rw [div_le_div_iff₀ (pow_pos hn 2) hden]
      have hsq : 4 * R' ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      have h1 : (4 / 3) * R' ^ 2 ≤ 3 * ‖x‖ ^ 2 := by nlinarith [hsq]
      have h2 : (4 / 3) * R' ^ 2 * ‖x‖ ^ 2 ≤ 12 * R' ^ 2 * ‖x‖ ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg R') (sq_nonneg ‖x‖)]
      have hmain : (4 / 3) * R' ^ 2 * (1 + ‖x‖ ^ 2)
          ≤ 3 * (1 + 4 * R' ^ 2) * ‖x‖ ^ 2 := by linarith
      have hMR : (0 : ℝ) ≤ M * R' := mul_nonneg hM hR'
      have hfin := mul_le_mul_of_nonneg_left hmain hMR
      nlinarith [hfin]
    · -- **near field**: `‖x‖ ≤ 2R'`, where the field is bounded by `3 M R'`
      have hb := Work.LWP.BiotSavart.norm_biotSavart_near hR' hM hg hsupp' hx
      have hsq : ‖x‖ ^ 2 ≤ 4 * R' ^ 2 := by nlinarith [norm_nonneg x]
      have hMR : (0 : ℝ) ≤ 3 * M * R' := mul_nonneg (mul_nonneg (by norm_num) hM) hR'
      refine hb.trans ?_
      rw [le_div_iff₀ hden]
      exact mul_le_mul_of_nonneg_left (by linarith) hMR

end Work.FTS.PressureOn
