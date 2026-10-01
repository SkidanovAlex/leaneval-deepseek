import Mathlib

namespace Work.LinnikAreas.BGTZ.E

/-- If `X > 0`, `C > 0`, `q > 0` and `log X ≤ log q / C` then `X ≤ q^{1/C}` (since `X = exp(log X) ≤ exp((log q)/C) = q^{1/C}`). -/
theorem LogConstLeRpow {q X C : ℝ} (hq : 0 < q) (hX : 0 < X) (hC : 0 < C)
    (h : Real.log X ≤ Real.log q / C) : X ≤ q ^ (1 / C : ℝ) := by
  calc X = Real.exp (Real.log X) := (Real.exp_log hX).symm
    _ ≤ Real.exp (Real.log q / C) := Real.exp_le_exp.mpr h
    _ = Real.exp (Real.log q * (1 / C)) := by rw [div_eq_mul_one_div]
    _ = q ^ (1 / C : ℝ) := (Real.rpow_def_of_pos hq (1 / C)).symm

end Work.LinnikAreas.BGTZ.E
