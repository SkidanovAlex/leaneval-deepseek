import Mathlib

namespace Work.ORHughesFree.NaturalExtension

/-- The normalized "leading ratio" sequence `n ↦ ((n+1) - c)/(n+1) * y`, where `c : ℤ` is a fixed
integer read in `ℝ`, tends to `y` and is bounded in absolute value by `(1 + |c|) * |y|`.

(The bound `max 1 |c| * |y|` suggested earlier is FALSE for negative `c`: `c = -1`, `y = 1`,
`n = 0` gives `2 ≤ 1`. The corrected bound below is valid for all `c : ℤ`: the ratio is at most
`1 + |c|/(n+1) ≤ 1 + |c|` in absolute value.) -/
theorem tendsto_leadingRatio (c : ℤ) (y : ℝ) :
    Filter.Tendsto (fun n : ℕ => ((((n+1 : ℤ) - c : ℤ) : ℝ) / ((n+1 : ℕ) : ℝ)) * y)
        Filter.atTop (nhds y) ∧
      ∀ n : ℕ,
        |((((n+1 : ℤ) - c : ℤ) : ℝ) / ((n+1 : ℕ) : ℝ)) * y| ≤ (1 + |(c : ℝ)|) * |y| := by
  -- Rewrite the leading ratio as `1 - c/(n+1)`.
  have key : ∀ n : ℕ, ((((n+1 : ℤ) - c : ℤ) : ℝ) / ((n+1 : ℕ) : ℝ))
      = 1 - (c : ℝ) / ((n+1 : ℕ) : ℝ) := by
    intro n
    rw [show ((((n+1 : ℤ) - c : ℤ) : ℝ)) = ((n+1 : ℕ) : ℝ) - (c:ℝ) by push_cast; ring]
    field_simp
  -- The correction term `c/(n+1)` tends to `0`.
  have h1 : Filter.Tendsto (fun n : ℕ => (c:ℝ)/((n+1:ℕ):ℝ)) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hlim : Filter.Tendsto (fun n : ℕ => (1:ℝ) - (c:ℝ)/((n+1:ℕ):ℝ)) Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub h1)
  constructor
  · have h := hlim.mul_const y
    simpa only [key, one_mul] using h
  · intro n
    rw [key n, abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg y)
    have htri : |(1:ℝ) - (c:ℝ)/((n+1:ℕ):ℝ)| ≤ 1 + |(c:ℝ)|/((n+1:ℕ):ℝ) := by
      have h := abs_add_le (1:ℝ) (-((c:ℝ)/((n+1:ℕ):ℝ)))
      rw [abs_neg, abs_div, abs_one, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n+1:ℕ):ℝ))] at h
      simpa [sub_eq_add_neg] using h
    have hle : (1:ℝ) + |(c:ℝ)|/((n+1:ℕ):ℝ) ≤ 1 + |(c:ℝ)| := by
      have hge : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by
        have : (1:ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        exact_mod_cast this
      have := div_le_self (abs_nonneg (c:ℝ)) hge
      linarith
    exact le_trans htri hle

end Work.ORHughesFree.NaturalExtension
