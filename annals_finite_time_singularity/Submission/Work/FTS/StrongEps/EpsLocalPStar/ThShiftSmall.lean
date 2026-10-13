import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `θ`-shift is small when `θ` is small.**  For `ε > 0` there is `θ₀ > 0` with

  `thShift θ p₂ = arctan (tan θ * exp (-p₂)) ∈ (0, π/4)`

for every `θ ∈ (0, θ₀)` and every `p₂` with `|p₂| ≤ ε`.  (`Work.FTS.StrongEps.thShift`.)

Route: `θ₀ := min (π/4) (arctan (exp (-ε))) > 0` works.  Lower bound: `tan θ > 0` for `θ > 0`
small and `exp (-p₂) > 0`, so the arctangent argument is positive; upper bound:
`arctan (tan θ * exp (-p₂)) ≤ arctan (tan θ * exp ε) < arctan 1 = π/4` because `exp (-p₂) ≤ exp ε`
(on `|p₂| ≤ ε`) and `tan` is strictly increasing below `π/2` with `tan (arctan (exp (-ε))) = exp (-ε)`,
so `θ < arctan (exp (-ε))` gives `tan θ * exp ε < 1`.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem ThShiftSmall {ε : ℝ} (hε : 0 < ε) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ ∈ Set.Ioo 0 θ₀, ∀ p₂ : ℝ, |p₂| ≤ ε →
      Work.FTS.StrongEps.thShift θ p₂ ∈ Set.Ioo 0 (Real.pi/4) := by
  -- `θ₀ := arctan (exp (-ε))` is positive, and `exp (-ε) < 1` (so `θ₀ < π/4`).
  have hexp_lt_one : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine ⟨Real.arctan (Real.exp (-ε)), Real.arctan_pos.mpr (Real.exp_pos _), ?_⟩
  intro θ hθ p₂ hp₂
  have hθ0 : 0 < θ := hθ.1
  have hθθ : θ < Real.arctan (Real.exp (-ε)) := hθ.2
  -- `θ < π/2`, so `tan θ > 0`
  have hθπ2 : θ < Real.pi / 2 := lt_trans hθθ (Real.arctan_lt_pi_div_two _)
  have htpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθπ2
  constructor
  · -- lower bound: the arctangent argument is positive
    rw [Work.FTS.StrongEps.thShift]
    exact Real.arctan_pos.mpr (mul_pos htpos (Real.exp_pos _))
  · -- upper bound: `tan θ * exp (-p₂) ≤ tan θ * exp ε < exp (-ε) * exp ε = 1`
    have htanθ : Real.tan θ < Real.exp (-ε) := by
      have h1 : Real.tan θ < Real.tan (Real.arctan (Real.exp (-ε))) :=
        Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos])
          (Real.arctan_lt_pi_div_two _) hθθ
      rwa [Real.tan_arctan] at h1
    have hexp_le : Real.exp (-p₂) ≤ Real.exp ε := by
      rw [Real.exp_le_exp]
      linarith [neg_le_abs p₂, hp₂]
    rw [Work.FTS.StrongEps.thShift, ← Real.arctan_one]
    apply Real.arctan_lt_arctan_iff.mpr
    calc Real.tan θ * Real.exp (-p₂) ≤ Real.tan θ * Real.exp ε :=
          mul_le_mul_of_nonneg_left hexp_le (le_of_lt htpos)
      _ < Real.exp (-ε) * Real.exp ε := mul_lt_mul_of_pos_right htanθ (Real.exp_pos ε)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Work.FTS.StrongEps.EpsLocalPStar
