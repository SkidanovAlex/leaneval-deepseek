import Mathlib
import Submission.Work.Pert.pert2v2.GatePreimageReBound.sum_exp_geom_bound

/-!
# `Work.Pert.pert2v2.GatePreimageReBound.walk_sum_bound`

A purely real threshold lemma for the gate walk.  There is a height `T` such that, for every
`t ≥ T` and every `n` with `n ≤ (32/31)(t + C)`, simultaneously

* every one of the `n` walk positions `t - j/32` (`j < n`) stays above `Ydec`, and
* the accumulated defect `∑_{j<n} M exp (-(κ (t - j/32)))` is at most `1`.

Both parts only need `t` large:

* the position part is the linear inequality `(t + C)/31 ≤ t - Ydec`, used through
  `j/32 < n/32 ≤ (t+C)/31` (from `j < n` and `n ≤ (32/31)(t+C)`);
* the sum part is the geometric bound `sum_exp_geom_bound`, whose right-hand side
  `A * exp (-((30/31) κ t))`, `A = M exp (κC/31)/(exp (κ/32) - 1)`, tends to `0`, hence is `≤ 1`
  for all large `t`.
-/

namespace Work.Pert.pert2v2.GatePreimageReBound

open Filter
open scoped Topology

/-- **Positions part of the walk threshold.**  If `t ≥ max 0 ((C + 31 Ydec)/30)` and
`n ≤ (32/31)(t + C)`, then all walk positions `t - j/32`, `j < n`, lie above `Ydec`. -/
theorem walk_positions_of_le (C Ydec t : ℝ) (n : ℕ)
    (ht : max 0 ((C + 31 * Ydec) / 30) ≤ t) (hn : (n : ℝ) ≤ (32 / 31) * (t + C)) :
    ∀ j : ℕ, j < n → Ydec < t - (j : ℝ) / 32 := by
  intro j hj
  -- `j/32 < n/32 ≤ (t + C)/31`
  have h1 : (j : ℝ) / 32 < (n : ℝ) / 32 :=
    div_lt_div_of_pos_right (by exact_mod_cast hj) (by norm_num : (0 : ℝ) < 32)
  have h2 : (n : ℝ) / 32 ≤ (t + C) / 31 := by
    have h := div_le_div_of_nonneg_right hn (by norm_num : (0 : ℝ) ≤ 32)
    have he : ((32 / 31 : ℝ) * (t + C)) / 32 = (t + C) / 31 := by ring
    rwa [he] at h
  -- `(t + C)/31 ≤ t - Ydec` for `t` above the linear threshold
  have h3 : (t + C) / 31 ≤ t - Ydec := by
    have htm : (C + 31 * Ydec) / 30 ≤ t := le_trans (le_max_right _ _) ht
    have h4 : C + 31 * Ydec ≤ t * 30 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 30)).mp htm
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 31)]
    linarith
  linarith

/-- **The walk threshold.**  There is `T` such that for all `t ≥ T` and all `n` with
`n ≤ (32/31)(t + C)`, the positions `t - j/32` (`j < n`) exceed `Ydec` and the accumulated defect
sum is `≤ 1`. -/
theorem walk_sum_bound (M κ C Ydec : ℝ) (hM : 0 < M) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ n : ℕ, (n : ℝ) ≤ (32 / 31) * (t + C) →
      (∀ j : ℕ, j < n → Ydec < t - (j : ℝ) / 32) ∧
      (∑ j ∈ Finset.range n, M * Real.exp (-(κ * (t - (j : ℝ) / 32)))) ≤ 1 := by
  -- the geometric bound `A * exp (-((30/31) κ t))` tends to `0`, hence is `≤ 1` eventually
  have hc : 0 < (30 / 31 : ℝ) * κ := by linarith
  have hlim : Tendsto (fun t : ℝ => (M * Real.exp (κ * C / 31) / (Real.exp (κ / 32) - 1))
        * Real.exp (-(((30 : ℝ) / 31) * κ * t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(((30 : ℝ) / 31) * κ * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
    simpa using h1.const_mul (M * Real.exp (κ * C / 31) / (Real.exp (κ / 32) - 1))
  obtain ⟨T2, hT2⟩ : ∃ T2 : ℝ, ∀ t : ℝ, T2 ≤ t →
      (M * Real.exp (κ * C / 31) / (Real.exp (κ / 32) - 1))
        * Real.exp (-((30 / 31 : ℝ) * κ * t)) ≤ 1 := by
    refine Filter.eventually_atTop.mp ?_
    exact hlim.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  refine ⟨max (max 0 ((C + 31 * Ydec) / 30)) T2, fun t ht n hn => ⟨?_, ?_⟩⟩
  · exact walk_positions_of_le C Ydec t n (le_trans (le_max_left _ _) ht) hn
  · exact le_trans (sum_exp_geom_bound M κ C hM hκ t n hn)
      (hT2 t (le_trans (le_max_right _ _) ht))

end Work.Pert.pert2v2.GatePreimageReBound
