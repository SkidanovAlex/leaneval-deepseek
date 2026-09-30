import Mathlib
import Submission.Work.BW.mvdefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The power series of `-log (1 - x)` for `|x| < 1` gives, after removing the
`m = 0` and `m = 1` terms and reindexing, the identity

`∑_{m} ε^{m+2}/(m+2) = log (1/(1-ε)) - ε`  for `0 ≤ ε < 1`. -/
theorem tsum_pow_div_shift {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (∑' m : ℕ, ε^(m+2)/((m:ℝ)+2)) = Real.log (1/(1-ε)) - ε := by
  have habs : |ε| < 1 := by rw [abs_of_nonneg hε0]; exact hε1
  have hlog : -Real.log (1 - ε) = Real.log (1/(1-ε)) := by
    have hne : (1:ℝ) - ε ≠ 0 := by linarith
    rw [Real.log_div one_ne_zero hne, Real.log_one]; ring
  -- the Mathlib Taylor series for `log`, stated with limit `log (1/(1-ε))`
  have hf : HasSum (fun n : ℕ => ε^(n+1)/((n:ℝ)+1)) (Real.log (1/(1-ε))) := by
    have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
    rw [hlog] at hsum
    exact hsum
  -- reindex the series by `n ↦ n + 1` and subtract the `n = 0` term `ε`
  have hfun : (fun n : ℕ => (fun k : ℕ => ε^(k+1)/((k:ℝ)+1)) (n+1))
      = fun n : ℕ => ε^(n+2)/((n:ℝ)+2) := by
    funext n
    change ε^((n+1)+1)/((((n+1) : ℕ) : ℝ)+1) = ε^(n+2)/((n:ℝ)+2)
    have h1' : (n+1)+1 = n+2 := by omega
    have h2' : (((n+1 : ℕ)) : ℝ) + 1 = (n:ℝ) + 2 := by push_cast; ring
    rw [h1', h2']
  have h3 : HasSum (fun n : ℕ => ε^(n+2)/((n:ℝ)+2)) (Real.log (1/(1-ε)) - ε) := by
    have key : HasSum (fun n : ℕ => (fun k : ℕ => ε^(k+1)/((k:ℝ)+1)) (n+1))
        (Real.log (1/(1-ε)) - ε) := by
      refine (hasSum_nat_add_iff (f := fun k : ℕ => ε^(k+1)/((k:ℝ)+1)) 1).mpr ?_
      have h0 : ∑ i ∈ Finset.range 1, ε^(i+1)/((i:ℝ)+1) = ε := by simp
      rw [h0]
      have : Real.log (1/(1-ε)) - ε + ε = Real.log (1/(1-ε)) := by ring
      rw [this]
      exact hf
    rwa [hfun] at key
  rw [h3.tsum_eq]

end Work.BW
