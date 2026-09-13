import Mathlib

namespace Commons.Algebra.Matrix

theorem gramForm_trace_det_id (E2 L2 EL η : ℝ) (hG : E2 * L2 - EL ^ 2 ≠ 0) :
    ((L2 * (3 * E2 - 2 * E2 ^ 2 - η * EL ^ 2) - 2 * EL * (3 * EL - 2 * E2 * EL - η * EL * L2) +
        E2 * (3 * L2 - 2 * EL ^ 2 - η * L2 ^ 2)) / (E2 * L2 - EL ^ 2) = 6 - 2 * E2 - η * L2) ∧
      (((3 * E2 - 2 * E2 ^ 2 - η * EL ^ 2) * (3 * L2 - 2 * EL ^ 2 - η * L2 ^ 2) -
          (3 * EL - 2 * E2 * EL - η * EL * L2) ^ 2) / (E2 * L2 - EL ^ 2) =
        9 - 6 * E2 - 3 * η * L2 + 2 * η * (E2 * L2 - EL ^ 2)) := by
  constructor
  · rw [div_eq_iff hG]; ring
  · rw [div_eq_iff hG]; ring

end Commons.Algebra.Matrix
