import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

/-- The "decay correction" inequality: for `0 < b`, `0 ≤ t ≤ τ`,
`1 - b/√(b²+t²) ≥ t²/(2(b²+τ²))`. -/
theorem one_sub_div_sqrt_sq_ge {b τ t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    1 - b/Real.sqrt (b^2+t^2) ≥ t^2/(2*(b^2+τ^2)) := by
  set st := Real.sqrt (b^2+t^2) with hst
  set sτ := Real.sqrt (b^2+τ^2) with hsτ
  have ht2 : 0 ≤ t^2 := sq_nonneg t
  have hτ2 : 0 ≤ τ^2 := sq_nonneg τ
  have hst_pos : 0 < st := by
    rw [hst]; exact Real.sqrt_pos.mpr (by positivity)
  have hsτ_pos : 0 < sτ := by
    rw [hsτ]; exact Real.sqrt_pos.mpr (by positivity)
  have hst_sq : st^2 = b^2 + t^2 := by
    rw [hst]; exact Real.sq_sqrt (by positivity)
  have hsτ_sq : sτ^2 = b^2 + τ^2 := by
    rw [hsτ]; exact Real.sq_sqrt (by positivity)
  have hst_ge_b : b ≤ st := by
    rw [hst]; exact (Real.le_sqrt hb.le (by positivity)).mpr (by nlinarith)
  have hsτ_ge_b : b ≤ sτ := by
    rw [hsτ]; exact (Real.le_sqrt hb.le (by positivity)).mpr (by nlinarith)
  have hst_le : st ≤ sτ := by
    rw [hst, hsτ]; exact Real.sqrt_le_sqrt (by nlinarith)
  have key : st * (st + b) ≤ 2 * (b^2 + τ^2) := by
    have h2 : st + b ≤ 2 * sτ := by linarith
    calc st * (st + b) ≤ sτ * (2 * sτ) := by
          apply mul_le_mul hst_le h2 (by linarith) (le_of_lt hsτ_pos)
    _ = 2 * (b^2 + τ^2) := by nlinarith [hsτ_sq]
  have hrewrite : 1 - b/st = t^2/(st*(st+b)) := by
    rw [eq_div_iff (by positivity)]
    field_simp
    nlinarith [hst_sq]
  have hfinal : t^2/(2*(b^2+τ^2)) ≤ t^2/(st*(st+b)) :=
    div_le_div_of_nonneg_left ht2 (by positivity) key
  calc t^2/(2*(b^2+τ^2)) ≤ t^2/(st*(st+b)) := hfinal
    _ = 1 - b/st := hrewrite.symm
    _ = 1 - b/Real.sqrt (b^2+t^2) := by rw [hst]

end Commons.Analysis.Real