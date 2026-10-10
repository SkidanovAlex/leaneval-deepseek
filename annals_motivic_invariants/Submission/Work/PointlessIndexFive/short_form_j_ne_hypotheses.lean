import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- For an elliptic curve in short normal form over a field of characteristic `≠ 2` with
`j ≠ 1728`, the coefficients `a₄` and `a₆` are not both zero, and we cannot have `a₄ ≠ 0`
together with `a₆ = 0` (the latter would force `j = 1728`). -/
theorem short_form_j_ne_hypotheses {𝕜 : Type} [Field 𝕜] (W : WeierstrassCurve 𝕜) [W.IsElliptic]
    [W.IsShortNF] (h2 : (2 : 𝕜) ≠ 0) (hj : W.j ≠ 1728) :
    (W.a₄ ≠ 0 ∨ W.a₆ ≠ 0) ∧ ¬ (W.a₄ ≠ 0 ∧ W.a₆ = 0) := by
  constructor
  · -- If both `a₄` and `a₆` vanished the discriminant would be zero, contradicting
    -- that the curve is elliptic.
    by_contra h
    simp only [not_or, not_ne_iff] at h
    obtain ⟨ha4, ha6⟩ := h
    have hΔ : W.Δ = 0 := by
      rw [WeierstrassCurve.Δ_of_isShortNF, ha4, ha6]
      first | refl_ring1 | ring
    exact (hΔ ▸ W.isUnit_Δ).ne_zero rfl
  · -- If `a₆ = 0` and `a₄ ≠ 0`, then `j = 6912 * a₄ ^ 3 / (4 * a₄ ^ 3) = 1728`.
    rintro ⟨ha4, ha6⟩
    apply hj
    rw [WeierstrassCurve.j_of_isShortNF, ha6]
    have h4 : (4 : 𝕜) ≠ 0 := by
      have : (4 : 𝕜) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have hden : 4 * W.a₄ ^ 3 + 27 * (0 : 𝕜) ^ 2 ≠ 0 := by
      rw [show (4 * W.a₄ ^ 3 + 27 * (0 : 𝕜) ^ 2) = 4 * W.a₄ ^ 3 by ring]
      exact mul_ne_zero h4 (pow_ne_zero 3 ha4)
    rw [div_eq_iff hden]
    first | refl_ring1 | ring

end Work.PointlessIndexFive
