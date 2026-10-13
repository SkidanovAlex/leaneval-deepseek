import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

open MeasureTheory Set

/-- For `c > 0` and `r > 0`, the function `θ ↦ c / θ` is not integrable on `(0, r)`:
the singularity at `θ = 0` is non-integrable (the primitive is `c · log θ → -∞`).
Equivalently, this is the borderline case `s = -1` of `integrableOn_Ioo_rpow_iff`: the
real power `θ ^ s` is integrable on `(0, r)` exactly for `-1 < s`. -/
theorem not_integrableOn_Ioo_div {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => c / θ) (Set.Ioo (0:ℝ) r) := by
  intro h
  -- multiplying by the nonzero constant `c⁻¹` reduces to the non-integrability of `θ⁻¹`
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => c⁻¹ * (c / θ)) (Set.Ioo (0:ℝ) r) :=
    h.const_mul c⁻¹
  have h3 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ⁻¹) (Set.Ioo (0:ℝ) r) :=
    h2.congr_fun (fun θ _ => by
      show c⁻¹ * (c / θ) = θ⁻¹
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]) measurableSet_Ioo
  -- `θ⁻¹` is the real power `θ ^ (-1)`
  have h4 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (-1 : ℝ)) (Set.Ioo (0:ℝ) r) :=
    h3.congr_fun (fun θ _ => by
      show θ⁻¹ = θ ^ (-1 : ℝ)
      rw [Real.rpow_neg_one]) measurableSet_Ioo
  -- whose integrability on `(0, r)` is equivalent to the false statement `-1 < -1`
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr] at h4
  exact absurd h4 (lt_irrefl (-1))

end Work.FTS.StrongPersist.H6Aux.EndLimits
