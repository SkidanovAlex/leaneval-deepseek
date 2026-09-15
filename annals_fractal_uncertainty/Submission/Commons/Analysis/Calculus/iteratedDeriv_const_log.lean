import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus

/-- The `(n+1)`-st iterated derivative of the real logarithm at a positive point. -/
theorem iteratedDeriv_succ_log_real {n : ℕ} {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (n + 1) Real.log x
      = (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * x ^ (-1 - (n : ℤ)) := by
  have h_eq : deriv Real.log =ᶠ[𝓝 x] Inv.inv := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y _
    rw [Real.deriv_log]
  rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq n h_eq, iteratedDeriv_eq_iterate,
    iter_deriv_inv]

theorem iteratedDeriv_const_log (c : ℝ) (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fun y : ℝ => c * Real.log y) x
      = c * (-1 : ℝ) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) * x ^ (-(k : ℤ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have hpull : iteratedDeriv (n + 1) (fun y : ℝ => c * Real.log y) x
      = c * iteratedDeriv (n + 1) Real.log x := by
    simp only [iteratedDeriv_const_mul_field]
  have hlog := iteratedDeriv_succ_log_real (n := n) hx
  have hz : (-(((n + 1 : ℕ) : ℤ))) = -1 - (n : ℤ) := by push_cast; ring
  rw [hpull, hlog, hz]
  ring_nf

end Commons.Analysis.Calculus