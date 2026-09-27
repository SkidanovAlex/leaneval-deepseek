import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.step10_bad_case
import Submission.Work.EKLC8Core.step10_second_choice
import Submission.Work.EKLC8Core.step10_upper

/-!
# Step 10: the "two choices" of the H-property dichotomy

`Work.EKLC8Core.step10_two_choice` is the conjunction of the case analysis of Step 10 of
`ROUTE_LEAD.md` §5.  If the first candidate `r₁ ∈ (ρκ⁻¹, κ⁻¹]` already has drift `≥ ρ²`
we take it (and `step10_upper` bounds it above); otherwise `step10_bad_case` upgrades the
failure of `r₁` into the lower bound `ρ²κ² ≤ |G 1 0|`, and `step10_second_choice` converts
that into drift `≥ ρ²` for the second candidate `r₂ ∈ ((ρ⁻¹)⁴κ⁻¹, (ρ⁻¹)⁵κ⁻¹]`, whose
upper bound is again `step10_upper`.
-/

namespace Work.EKLC8Core

theorem step10_two_choice {ρ κ r₁ r₂ : ℝ} {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hκ : 0 < κ) (hκκ : kappa G = κ)
    (hr₁1 : ρ * κ⁻¹ < |r₁|) (hr₁2 : |r₁| ≤ κ⁻¹)
    (hr₂1 : (ρ⁻¹) ^ 4 * κ⁻¹ < |r₂|) (hr₂2 : |r₂| ≤ (ρ⁻¹) ^ 5 * κ⁻¹) :
    (ρ ^ 2 ≤ drift G r₁ ∧ drift G r₁ ≤ 2 * (ρ⁻¹) ^ 10) ∨
    (ρ ^ 2 ≤ drift G r₂ ∧ drift G r₂ ≤ 2 * (ρ⁻¹) ^ 10) := by
  have hρ1' : ρ ≤ 1 := by linarith
  have hκinv : κ⁻¹ * κ = 1 := inv_mul_cancel₀ (ne_of_gt hκ)
  have hpow : (1 : ℝ) ≤ (ρ⁻¹) ^ 5 := one_le_pow₀ (one_le_inv₀ hρ0 |>.mpr hρ1')
  rcases lt_or_ge (drift G r₁) (ρ ^ 2) with hlt | hge
  · -- the first candidate fails, so the second one must work
    right
    have hbad := step10_bad_case hρ0 hρ1 hκ hκκ hr₁1 hr₁2 hlt
    have hlow : ρ ^ 2 ≤ drift G r₂ :=
      step10_second_choice hρ0 hρ1 hκ hκκ hbad hr₂1 hr₂2
    refine ⟨hlow, ?_⟩
    have hr : |r₂| * κ ≤ (ρ⁻¹) ^ 5 := by
      calc |r₂| * κ ≤ ((ρ⁻¹) ^ 5 * κ⁻¹) * κ := mul_le_mul_of_nonneg_right hr₂2 hκ.le
        _ = (ρ⁻¹) ^ 5 := by rw [mul_assoc, hκinv, mul_one]
    exact (step10_upper hρ0 hρ1' hκ hκκ hr).1
  · -- the first candidate already has drift `≥ ρ²`
    left
    refine ⟨hge, ?_⟩
    have hr : |r₁| * κ ≤ (ρ⁻¹) ^ 5 := by
      calc |r₁| * κ ≤ κ⁻¹ * κ := mul_le_mul_of_nonneg_right hr₁2 hκ.le
        _ = 1 := hκinv
        _ ≤ (ρ⁻¹) ^ 5 := hpow
    exact (step10_upper hρ0 hρ1' hκ hκκ hr).1

end Work.EKLC8Core
