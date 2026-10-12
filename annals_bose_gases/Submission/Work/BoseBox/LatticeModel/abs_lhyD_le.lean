import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.LatticeModel.LhyAuxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The bound `|lhyD c r| ≤ c²/r³`

`lhyD c r = 2r − 2(r²+c)/√(r²+2c) + c²/r³` is the derivative of the
rationalised Bogoliubov bracket `lhyF c` (see `LhyAuxDefs`).  Writing

`lhyD c r = c²/r³ − 2·h(r)`,   `h(r) = (r²+c)/√(r²+2c) − r`,

the assertion `|lhyD c r| ≤ c²/r³` is exactly `0 ≤ h(r) ≤ c²/r³`.

* `h(r) ≥ 0` is `r·√(r²+2c) ≤ r²+c`, which after squaring is `c² ≥ 0`.
* `h(r) ≤ c²/r³`: rationalising the difference
  `((r²+c) − r√(r²+2c))((r²+c) + r√(r²+2c)) = c²` gives
  `h(r) = c² / (√(r²+2c)·((r²+c) + r√(r²+2c)))`, and the denominator is
  `≥ r·r²` because `√(r²+2c) ≥ r` and `(r²+c) + r√(r²+2c) ≥ r²`.
-/

noncomputable section

open scoped Real

namespace Work.BoseBox.LatticeModel

/-- Auxiliary square-root bound used in `abs_lhyD_le`. -/
private lemma sqrtsq_add : ∀ r c : ℝ, 0 < c → 0 < r →
    r * Real.sqrt (r ^ 2 + 2 * c) ≤ r ^ 2 + c := by
  intro r c hc hr
  have hs_sq : (Real.sqrt (r ^ 2 + 2 * c)) ^ 2 = r ^ 2 + 2 * c :=
    Real.sq_sqrt (by nlinarith)
  have hsq : (r * Real.sqrt (r ^ 2 + 2 * c)) ^ 2 ≤ (r ^ 2 + c) ^ 2 := by
    rw [mul_pow, hs_sq]
    nlinarith [sq_nonneg c]
  have h1 : |r * Real.sqrt (r ^ 2 + 2 * c)| ≤ |r ^ 2 + c| := sq_le_sq.mp hsq
  rw [abs_of_nonneg (mul_nonneg hr.le (Real.sqrt_nonneg _)),
      abs_of_nonneg (by nlinarith [sq_nonneg r, hc])] at h1
  exact h1

theorem abs_lhyD_le (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    |lhyD c r| ≤ c ^ 2 / r ^ 3 := by
  set s := Real.sqrt (r ^ 2 + 2 * c) with hs_def
  have hs_sq : s ^ 2 = r ^ 2 + 2 * c := by
    rw [hs_def]; exact Real.sq_sqrt (by nlinarith)
  have hs_pos : 0 < s := by
    rw [hs_def]; exact Real.sqrt_pos.mpr (by nlinarith)
  have hs_ge : r ≤ s := by
    have h := Real.sqrt_le_sqrt (show r ^ 2 ≤ r ^ 2 + 2 * c by nlinarith)
    rw [Real.sqrt_sq hr.le, ← hs_def] at h
    exact h
  -- The derivative as `c²/r³` minus twice the "defect" `h = (r²+c)/s − r`.
  have key : lhyD c r = c ^ 2 / r ^ 3 - 2 * (((r ^ 2 + c) / s) - r) := by
    simp only [lhyD]
    rw [← hs_def]
    ring
  -- `r·s ≤ r²+c`, i.e. the defect is nonnegative.
  have hrs_le : r * s ≤ r ^ 2 + c := by
    have := sqrtsq_add r c hc hr
    rw [← hs_def] at this
    exact this
  have hu_nonneg : 0 ≤ (r ^ 2 + c) - r * s := by linarith
  have hW_pos : 0 < (r ^ 2 + c) + r * s := by
    nlinarith [sq_nonneg r, hc, mul_nonneg hr.le hs_pos.le]
  -- Rationalisation of the defect.
  have hident : ((r ^ 2 + c) - r * s) * ((r ^ 2 + c) + r * s) = c ^ 2 := by
    nlinarith [hs_sq]
  have h_eq : (r ^ 2 + c) / s - r = ((r ^ 2 + c) - r * s) / s := by
    rw [eq_div_iff (ne_of_gt hs_pos), sub_mul, div_mul_cancel₀ _ (ne_of_gt hs_pos)]
  have hu_eq : ((r ^ 2 + c) - r * s) / s
      = c ^ 2 / (((r ^ 2 + c) + r * s) * s) := by
    rw [div_eq_div_iff (ne_of_gt hs_pos) (ne_of_gt (mul_pos hW_pos hs_pos))]
    nlinarith [hident]
  -- The denominator `((r²+c)+rs)·s` is at least `r³`.
  have hWs : r ^ 3 ≤ ((r ^ 2 + c) + r * s) * s := by
    have hWs1 : r ^ 2 ≤ (r ^ 2 + c) + r * s := by
      nlinarith [mul_nonneg hr.le hs_pos.le, hc]
    calc r ^ 3 = r ^ 2 * r := by ring
      _ ≤ ((r ^ 2 + c) + r * s) * s := mul_le_mul hWs1 hs_ge hr.le hW_pos.le
  have h_le_u : ((r ^ 2 + c) - r * s) / s ≤ c ^ 2 / r ^ 3 := by
    rw [hu_eq]
    exact div_le_div_of_nonneg_left (sq_nonneg c) (by positivity) hWs
  have h_nonneg : 0 ≤ (r ^ 2 + c) / s - r := by
    rw [h_eq]; exact div_nonneg hu_nonneg hs_pos.le
  have h_le : (r ^ 2 + c) / s - r ≤ c ^ 2 / r ^ 3 := by
    rw [h_eq]; exact h_le_u
  rw [key]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

end Work.BoseBox.LatticeModel
