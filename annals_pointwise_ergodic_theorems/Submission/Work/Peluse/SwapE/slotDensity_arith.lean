import Mathlib
import Submission.Work.Peluse.SwapE.Defs

namespace Work.Peluse.SwapE

/-- **Arithmetic of the slot-density constant.**

With `endgameK0 η H M = 24/η² + 8H/M`, any `x` bounded by
`4/(η²HM) + 1/M²` (the two-line count of KKL Corollary 7.2 plus the `1/M²` correction) is
bounded by `endgameK0 η H M / (4HM+1)`.  The two summands are estimated separately against
the two terms of `endgameK0`:

* `4/(η²HM) ≤ (24/η²)/(4HM+1)`, since `4HM+1 ≤ 6HM` for `HM ≥ 1`;
* `1/M² ≤ (8H/M)/(4HM+1)`, since `4HM+1 ≤ 8HM` for `HM ≥ 1`,

and `a/c + b/c = (a+b)/c`. -/
theorem slotDensity_arith (η : ℝ) (H M : ℕ) (x : ℝ)
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hη : 0 < η)
    (hx : x ≤ 4 / (η ^ 2 * (H : ℝ) * (M : ℝ)) + 1 / (M : ℝ) ^ 2) :
    x ≤ endgameK0 η H M / (4 * (H : ℝ) * (M : ℝ) + 1) := by
  have hH' : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hHM1 : (1 : ℝ) ≤ (H : ℝ) * (M : ℝ) := by
    simpa using mul_le_mul hH' hM' (by norm_num) (by positivity)
  have hHMpos : (0 : ℝ) < η ^ 2 * (H : ℝ) * (M : ℝ) := by positivity
  have hId : (0 : ℝ) < η ^ 2 * (4 * (H : ℝ) * (M : ℝ) + 1) := by positivity
  have h1 : 4 / (η ^ 2 * (H : ℝ) * (M : ℝ)) ≤
      (24 / η ^ 2) / (4 * (H : ℝ) * (M : ℝ) + 1) := by
    rw [div_div, div_le_iff₀ hHMpos, div_mul_eq_mul_div, le_div_iff₀ hId]
    nlinarith [hη, hHM1]
  have h2 : 1 / (M : ℝ) ^ 2 ≤
      (8 * (H : ℝ) / (M : ℝ)) / (4 * (H : ℝ) * (M : ℝ) + 1) := by
    rw [div_div]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (M:ℝ)^2), div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0:ℝ) < (M:ℝ) * (4 * (H : ℝ) * (M : ℝ) + 1))]
    nlinarith [hη, hH', hM']
  have hstep : 4 / (η ^ 2 * (H : ℝ) * (M : ℝ)) + 1 / (M : ℝ) ^ 2
      ≤ (24 / η ^ 2 + 8 * (H : ℝ) / (M : ℝ)) / (4 * (H : ℝ) * (M : ℝ) + 1) := by
    calc 4 / (η ^ 2 * (H : ℝ) * (M : ℝ)) + 1 / (M : ℝ) ^ 2
        ≤ (24 / η ^ 2) / (4 * (H : ℝ) * (M : ℝ) + 1)
          + (8 * (H : ℝ) / (M : ℝ)) / (4 * (H : ℝ) * (M : ℝ) + 1) := add_le_add h1 h2
      _ = (24 / η ^ 2 + 8 * (H : ℝ) / (M : ℝ)) / (4 * (H : ℝ) * (M : ℝ) + 1) := by
          rw [add_div]
  calc x ≤ 4 / (η ^ 2 * (H : ℝ) * (M : ℝ)) + 1 / (M : ℝ) ^ 2 := hx
    _ ≤ (24 / η ^ 2 + 8 * (H : ℝ) / (M : ℝ)) / (4 * (H : ℝ) * (M : ℝ) + 1) := hstep
    _ = endgameK0 η H M / (4 * (H : ℝ) * (M : ℝ) + 1) := by rw [endgameK0]

end Work.Peluse.SwapE
