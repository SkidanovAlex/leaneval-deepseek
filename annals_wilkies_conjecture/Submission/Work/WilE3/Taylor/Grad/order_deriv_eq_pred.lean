import Mathlib

namespace Work.WilE3.Taylor.Grad

theorem order_deriv_eq_pred {f : ℝ → ℝ} {m : ℕ} (hf : AnalyticAt ℝ f 0) (hm : 0 < m)
    (hord : analyticOrderAt f 0 = (m : ℕ∞)) :
    f 0 = 0 ∧ analyticOrderAt (deriv f) 0 = ((m - 1 : ℕ) : ℕ∞) := by
  -- The function vanishes at `0`: the order-`m` decomposition forces `iteratedDeriv 0 f 0 = 0`.
  have hf0 : f 0 = 0 := by
    have h := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf (n := m)).mp hord
    have h0 := h.1 0 hm
    simpa using h0
  refine ⟨hf0, ?_⟩
  -- `analyticOrderAt_deriv_eq_iff` shifts the order by one, and `(m - 1) + 1 = m` since `m > 0`.
  have hcast : ((m - 1 : ℕ) : ℕ∞) + 1 = (m : ℕ∞) := by
    have h : (m - 1 : ℕ) + 1 = m := Nat.sub_add_cancel (Nat.one_le_of_lt hm)
    exact_mod_cast h
  have hiff := analyticOrderAt_deriv_eq_iff hf hf0 (n := m - 1)
  rw [hcast] at hiff
  exact hiff.mp hord

end Work.WilE3.Taylor.Grad
