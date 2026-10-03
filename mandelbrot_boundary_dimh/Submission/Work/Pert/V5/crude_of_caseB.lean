import Mathlib

namespace Work.Pert.V5

theorem crude_of_caseB {Ξ rr M Kp Rde ℓ : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hKp : 0 ≤ Kp) (hM : 2 ^ 10 ≤ M) (hRde : 11 * M ≤ Rde)
    (hpin : Ξ + 2 * Rde ≤ M + 2 * (Kp * (1 + Real.log (2 + M))))
    (hlen : ℓ ≤ Kp * (1 + Real.log (2 + M)) + M + Ξ + 2 ^ 10) :
    1025 * ℓ < 2 ^ 37 * (Kp * (1 + Real.log (2 + M))) := by
  -- With `L := Kp * (1 + log (2 + M))`: `hpin` and `hRde` give `Ξ ≤ 2L - 21M`,
  -- so `ℓ ≤ L + M + Ξ + 2^10 < 3L`, while `1025 * 3 = 3075 < 2^37` and `L ≥ 0`.
  have hlog : (0 : ℝ) ≤ Real.log (2 + M) := by
    apply Real.log_nonneg; linarith
  have hLnn : (0 : ℝ) ≤ Kp * (1 + Real.log (2 + M)) := by nlinarith [hKp, hlog]
  have hΞle : Ξ ≤ 2 * (Kp * (1 + Real.log (2 + M))) - 21 * M := by linarith
  have hlen3 : ℓ < 3 * (Kp * (1 + Real.log (2 + M))) := by linarith
  have hstep : 3075 * (Kp * (1 + Real.log (2 + M)))
      ≤ 2 ^ 37 * (Kp * (1 + Real.log (2 + M))) := by
    have hc : (3075 : ℝ) ≤ 2 ^ 37 := by norm_num
    nlinarith [hLnn, hc]
  have h1 : 1025 * ℓ < 3075 * (Kp * (1 + Real.log (2 + M))) := by nlinarith [hlen3]
  linarith

end Work.Pert.V5
