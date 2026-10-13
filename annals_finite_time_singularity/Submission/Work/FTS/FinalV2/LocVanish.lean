import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocData6.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.LocVanish` — the datum `locG6` vanishes at the θ-ends (curric-46 lead, 2026-10-10)

`locG6 α L β = locR α L β (z) · Γ(θ)` (`LocDataExt.locG_eq_locR_Gam`) with
`Γ α θ = (sin θ · cos² θ)^(α/3)` (`Work.Spaces.Gam`). At `θ = 0` (`sin 0 = 0`) and `θ = π/2`
(`cos (π/2) = 0`) the base is `0`, and `0 ^ (α/3) = 0` since `α/3 ≠ 0` for `α > 0`
(`Real.zero_rpow`). This supplies the hypothesis `hvan` of `StrongEps.EpsUniform_of_data` in
`Inputs'` (3) for the datum of the adapter.
-/

noncomputable section
open scoped Real

namespace Work.FTS.FinalV2

set_option autoImplicit false

theorem gam_zero_end {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  simp only [Work.Spaces.Gam, Real.sin_zero, zero_mul]
  exact Real.zero_rpow (by positivity)

theorem gam_pi_div_two_end {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α (π / 2) = 0 := by
  simp only [Work.Spaces.Gam, Real.cos_pi_div_two]
  rw [show Real.sin (π / 2) * (0 : ℝ) ^ 2 = 0 by ring]
  exact Real.zero_rpow (by positivity)

/-- **The datum vanishes at both θ-ends**, for every `z`. -/
theorem locG6_vanish {α : ℝ} (hα : 0 < α) (L β : ℝ) :
    ∀ z, 0 ≤ z → Work.FTS.LocData6.locG6 α L β z 0 = 0 ∧
      Work.FTS.LocData6.locG6 α L β z (π / 2) = 0 := by
  intro z _
  rw [Work.FTS.LocData6.locG6_eq, Work.FTS.LocDataExt.locG_eq_locR_Gam]
  exact ⟨by simp only [gam_zero_end hα, mul_zero], by simp only [gam_pi_div_two_end hα, mul_zero]⟩

end Work.FTS.FinalV2
