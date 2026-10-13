import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.biotSavart_decay
import Submission.Work.LWP.BiotSavart.farField_decay_const
import Submission.Work.LWP.BiotSavart.nearField_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **Explicit-constant far-field decay of the Biot–Savart field.**  For `g` bounded by `M ≥ 0` and
supported in the closed ball of radius `R ≥ 0`, the Biot–Savart field satisfies
`‖biotSavart g x‖ ≤ 3 M R (1 + 4R²)/(1 + ‖x‖²)` for every `x`.  This is the explicit-constant form of
`Work.FTS.PressureOn.biotSavart_decay`, which only produces an existential constant; the proof is the
same glue of `Work.LWP.BiotSavart.norm_biotSavart_near` (near field `‖x‖ ≤ 2R`, bound `3MR`) and
`Work.LWP.BiotSavart.farField_decay_const` (far field `2R ≤ ‖x‖`, bound `(4/3)MR³/‖x‖²`). -/
theorem biotSavartDecayExplicit {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hg : ∀ y, ‖g y‖ ≤ M)
    (hsupp : ∀ y, g y ≠ 0 → y ∈ Metric.closedBall 0 R) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖Work.LWP.biotSavart g x‖ ≤ 3 * M * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := by
  have hden : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  rcases lt_or_ge (2 * R) ‖x‖ with hx | hx
  · -- **far field** `2R < ‖x‖`: the field decays like `‖x‖⁻²`, and the two weights are comparable
    have hx' : 2 * R ≤ ‖x‖ := le_of_lt hx
    have hn : (0 : ℝ) < ‖x‖ := by linarith
    have hb := Work.LWP.BiotSavart.farField_decay_const hR hM hg hsupp x hx'
    refine hb.trans ?_
    rw [div_le_div_iff₀ (pow_pos hn 2) hden]
    -- goal: `(4/3)·M·R³·(1+‖x‖²) ≤ 3·M·R·(1+4R²)·‖x‖²`
    have hsq : 4 * R ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hmain : (4 / 3) * R ^ 2 * (1 + ‖x‖ ^ 2)
        ≤ 3 * (1 + 4 * R ^ 2) * ‖x‖ ^ 2 := by nlinarith [hsq, sq_nonneg R, sq_nonneg ‖x‖]
    have hMR : (0 : ℝ) ≤ M * R := mul_nonneg hM hR
    have hfin := mul_le_mul_of_nonneg_left hmain hMR
    nlinarith [hfin]
  · -- **near field** `‖x‖ ≤ 2R`: the field is bounded by `3MR` and the weight is `≥ 1`
    have hb := Work.LWP.BiotSavart.norm_biotSavart_near hR hM hg hsupp hx
    have hsq : ‖x‖ ^ 2 ≤ 4 * R ^ 2 := by nlinarith [norm_nonneg x]
    have hMR : (0 : ℝ) ≤ 3 * M * R := mul_nonneg (mul_nonneg (by norm_num) hM) hR
    refine hb.trans ?_
    rw [le_div_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (by linarith) hMR

end Work.FTS.PressureOn
