import Mathlib.Analysis.MeanInequalities

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

/-- For `0 < α ≤ 1` and `0 ≤ s ≤ 1` the quantity `s ^ (1 - α / 5) / (α + s)` is at most `2`.

In fact it is at most `1`: writing `δ = α/5 ∈ (0, 1/5]` and using the weighted AM–GM
inequality (concavity of `x ↦ x ^ δ`) in the form `y ^ δ ≤ δ * y + (1 - δ)` for `y ≥ 0`
with `y = 1/s` gives `s ^ (1 - δ) ≤ s + δ * (1 - s) ≤ s + α`, whence
`s ^ (1 - α/5) / (α + s) ≤ 1`. -/
theorem sin_rpow_slack {α s : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ (1 - α / 5) / (α + s) ≤ 2 := by
  have hδ0 : 0 ≤ α / 5 := by linarith
  rcases eq_or_lt_of_le hs0 with hs | hs
  · subst hs
    rw [Real.zero_rpow (by intro h; linarith), zero_div]
    norm_num
  · have hαs : 0 < α + s := by linarith
    -- weighted AM–GM with weights `α/5` and `1 - α/5` applied to `1/s` and `1`
    have hamgm : (1 / s) ^ (α / 5) * (1 : ℝ) ^ (1 - α / 5)
        ≤ (α / 5) * (1 / s) + (1 - α / 5) * 1 :=
      Real.geom_mean_le_arith_mean2_weighted hδ0 (by linarith) (by positivity) (by norm_num)
        (by ring)
    have hamgm' : (1 / s) ^ (α / 5) ≤ (α / 5) * (1 / s) + (1 - α / 5) := by
      simpa using hamgm
    -- `s ^ (1 - α/5) = s * (1/s) ^ (α/5)`
    have hsp : s ^ (1 - α / 5) = s * (1 / s) ^ (α / 5) := by
      rw [Real.rpow_sub hs, Real.rpow_one, one_div, Real.inv_rpow hs0, div_eq_mul_inv]
    have h1 : s * ((α / 5) * (1 / s)) = α / 5 := by
      field_simp
    have h2 : s * (1 - α / 5) ≤ s := by
      have hle : 1 - α / 5 ≤ 1 := by linarith
      simpa using mul_le_mul_of_nonneg_left hle hs0
    have hfin : s * ((α / 5) * (1 / s) + (1 - α / 5)) ≤ α + s := by
      rw [mul_add, h1]
      linarith
    -- the key estimate `s ^ (1 - α/5) ≤ α + s`
    have hkey : s ^ (1 - α / 5) ≤ α + s := by
      rw [hsp]
      exact le_trans (mul_le_mul_of_nonneg_left hamgm' hs0) hfin
    have hle1 : s ^ (1 - α / 5) / (α + s) ≤ 1 := by
      have := div_le_div_of_nonneg_right hkey hαs.le
      rwa [div_self (ne_of_gt hαs)] at this
    linarith

end Work.FTS.PhiStar
