import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Filter

/-- For a nonnegative real `c`, the function `T ↦ min 1 (1 / (T * c))` tends to `0` as `T → ∞`.
This is the per-term estimate used in the Perron-truncation error: the term is bounded by
`1 / (T * c)`, which goes to zero, and `min 1 ·` is continuous at `0`. -/
lemma tendsto_min_one_div_mul (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun T : ℝ => min 1 (1 / (T * c))) atTop (nhds 0) := by
  have h1 : Tendsto (fun T : ℝ => (T * c)⁻¹) atTop (nhds 0) := by
    rcases eq_or_lt_of_le hc with h | h
    · subst h; simp
    · have hmul : Tendsto (fun T : ℝ => T * c) atTop atTop := tendsto_id.atTop_mul_const h
      exact hmul.inv_tendsto_atTop
  have h2 : Tendsto (fun T : ℝ => min 1 ((T * c)⁻¹)) atTop (nhds (min 1 0)) :=
    (tendsto_const_nhds (x := (1 : ℝ))).min h1
  simpa [one_div] using h2

theorem perron_error_tendsto (y : ℝ) (hy : 0 < y) (Sf : Finset ℕ)
    (hn : ∀ n ∈ Sf, (n : ℝ) ≠ y) :
    Filter.Tendsto (fun T : ℝ => ∑ n ∈ Sf,
        (32 / (2 * Real.pi)) * (y / (n : ℝ)) * min 1 (1 / (T * |Real.log (y / (n : ℝ))|)))
      Filter.atTop (nhds 0) := by
  have hsum : Tendsto (fun T : ℝ => ∑ n ∈ Sf,
        (32 / (2 * Real.pi)) * (y / (n : ℝ)) * min 1 (1 / (T * |Real.log (y / (n : ℝ))|)))
      atTop (nhds (∑ _n ∈ Sf, (0 : ℝ))) := by
    refine tendsto_finsetSum Sf ?_
    intro n hn'
    have hc : (0 : ℝ) ≤ |Real.log (y / (n : ℝ))| := abs_nonneg _
    have h := tendsto_min_one_div_mul _ hc
    simpa using h.const_mul ((32 / (2 * Real.pi)) * (y / (n : ℝ)))
  simpa using hsum

end Work.BMF
