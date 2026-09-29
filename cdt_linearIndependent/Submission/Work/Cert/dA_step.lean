import Mathlib
import Submission.Work.Cert.aLoop_aux
import Submission.Work.Cert.cx_mul_le

namespace Work.Cert

/-- **One step of the `dA` budget of the `A`-loop invariant.**

`Bd k` is the accumulated rounding allowance `Σ_{j<k} (8·tri(j+1)+1)` and `BdM m rq k` the
accumulated mean-value budget `Σ_{j<k} tri(j+1)·μ^{tri(j+1)-1}·rq`, `μ = mub m = m/S`.  The step
`k → k+1` adds the rounding allowance `8·tri(k+1)+1` and the mean-value term
`tri(k+1)·μ^{tri(k+1)-1}·rq`; the loop pays for it with the new summand `mu (T * dvu mT' m) rq`
(the `+8*T+1` added to `dA` at this step cancels the new rounding allowance, `T = tri (k+1)`).
Since `mu x y ≥ x*y/S` and `dvu mT' m ≥ mT'*S/m`,
`mu (T * dvu mT' m) rq ≥ T * (mT'/S)/μ * rq ≥ T * μ^{tri (k+1) - 1} * rq`, using the lower bound
`μ^{tri (k+1)} ≤ mT'/S` on the new `mT` mantissa. -/
theorem dA_step (k : ℕ) (hk : 1 ≤ k) (m rq T mT' dA : ℤ)
    (hT : T = (tri (k + 1) : ℤ))
    (hdA : Bd k + BdM m rq k ≤ (dA : ℝ))
    (hmT : (mub m) ^ (tri (k + 1)) ≤ (mT' : ℝ) / ((S : ℝ)))
    (hm : 1 ≤ m) (hrq : 0 ≤ rq) :
    Bd (k + 1) + BdM m rq (k + 1) ≤
      (dA : ℝ) + ((mu (T * dvu mT' m) rq : ℤ) : ℝ) + 8 * (T : ℝ) + 1 := by
  rw [Bd_succ, BdM_succ]
  set N := tri (k + 1) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact tri_pos (by omega)
  have hrqR : (0:ℝ) ≤ (rq:ℝ) := by exact_mod_cast hrq
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast (lt_of_lt_of_le Int.zero_lt_one hm)
  have hT' : (T:ℝ) = (N:ℝ) := by rw [hT]; simp
  have hSpos : (0:ℝ) < (S:ℝ) := thS_pos
  have hmul_inv : mub m * ((S:ℝ)/(m:ℝ)) = 1 := by
    rw [mub]; field_simp
  obtain ⟨j, hj⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  have hstep : (mub m) ^ N * ((S:ℝ)/(m:ℝ)) = (mub m) ^ (N - 1) := by
    rw [hj, show j + 1 - 1 = j from by omega, pow_succ, mul_assoc, hmul_inv, mul_one]
  -- the new mantissa lower bound, scaled by `S/m > 0`, gives `μ^{N-1} ≤ mT'/m`
  have hkey : (mub m) ^ (N - 1) ≤ ((dvu mT' m : ℤ) : ℝ) / (S : ℝ) := by
    have hSdivm : (0:ℝ) ≤ (S:ℝ)/(m:ℝ) := div_nonneg (le_of_lt hSpos) (le_of_lt hmR)
    have h1 := mul_le_mul_of_nonneg_right hmT hSdivm
    rw [hstep] at h1
    have h2 : (mT' : ℝ) / (S:ℝ) * ((S:ℝ)/(m:ℝ)) = (mT':ℝ)/(m:ℝ) := by field_simp
    rw [h2] at h1
    have hdvu := dvu_ge' mT' m (by omega : (0:ℤ) < m)
    have h3 : ((mT':ℝ) * (S:ℝ) / (m:ℝ)) / (S:ℝ) = (mT':ℝ)/(m:ℝ) := by field_simp
    have h4 : (mT':ℝ)/(m:ℝ) ≤ ((dvu mT' m : ℤ):ℝ)/(S:ℝ) := by
      have := div_le_div_of_nonneg_right hdvu (le_of_lt hSpos)
      rwa [h3] at this
    linarith
  -- the loop's new summand covers the new mean-value term
  have hmain : (N : ℝ) * (mub m) ^ (N - 1) * (rq : ℝ) ≤ ((mu (T * dvu mT' m) rq : ℤ) : ℝ) := by
    have hge := mu_ge' (T * dvu mT' m) rq
    have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
    have ha : (mub m) ^ (N - 1) * (rq:ℝ) ≤ ((dvu mT' m : ℤ):ℝ)/(S:ℝ) * (rq:ℝ) :=
      mul_le_mul_of_nonneg_right hkey hrqR
    have hb : (N:ℝ) * ((mub m) ^ (N - 1) * (rq:ℝ)) ≤
        (N:ℝ) * (((dvu mT' m : ℤ):ℝ)/(S:ℝ) * (rq:ℝ)) := mul_le_mul_of_nonneg_left ha hNnn
    have h2 : (N:ℝ) * (((dvu mT' m : ℤ):ℝ)/(S:ℝ) * (rq:ℝ)) =
        ((T * dvu mT' m : ℤ):ℝ) * (rq:ℝ) / (S:ℝ) := by
      rw [hT]; push_cast; field_simp
    rw [h2] at hb
    have hb' : (N:ℝ) * (mub m) ^ (N - 1) * (rq:ℝ) ≤
        ((T * dvu mT' m : ℤ):ℝ) * (rq:ℝ) / (S:ℝ) := by
      rw [mul_assoc]; exact hb
    linarith
  -- the `8*T+1` chosen at this step is exactly the new rounding allowance
  have hcast : ((((8 * N + 1 : ℕ)) : ℝ)) = 8 * (T : ℝ) + 1 := by
    push_cast; rw [hT']
  linarith [hdA, hmain, hcast]

end Work.Cert
