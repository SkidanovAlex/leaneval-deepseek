import Mathlib

namespace Work.WilE3.Taylor.CaseII

theorem sum_dv_mul_grad_eq_zero {k : ℕ} {v g dv : Fin k → ℝ}
    (hv : v ≠ 0)
    (hmin : ∀ i j : Fin k, g i * v j - g j * v i = 0)
    (hcon : ∑ i, v i * dv i = 0) :
    ∑ i, dv i * g i = 0 := by
  -- Since 0 ≠ v, there is an index j0 with v j0 ≠ 0.
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hv
  -- The proportionality relations force g = c • v with c = g j0 / v j0.
  set c := g j0 / v j0 with hc
  have hg : ∀ i, g i = c * v i := by
    intro i
    have h1 : g i * v j0 = g j0 * v i := by linarith [hmin i j0]
    rw [hc, div_mul_eq_mul_div, eq_div_iff hj0]
    exact h1
  calc ∑ i, dv i * g i = ∑ i, c * (v i * dv i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hg i]; ring
    _ = c * ∑ i, v i * dv i := by rw [Finset.mul_sum]
    _ = 0 := by rw [hcon, mul_zero]

end Work.WilE3.Taylor.CaseII
