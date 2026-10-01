/-
# The Perron truncation error `perrErr` tends to zero as `T → ∞`

`perrErr ψ β x T = Σ_n λ(n) n^{-(1+β)} min(1, 1/(T |log(x/n)|))` is the standard majorant of
the truncation error of the Perron formula (see `Work.LinnikAreas.LoneLowerDefs`).  For every
real `β > 0` and `x > 0` it tends to `0` as `T → +∞`: the pointwise factors
`min(1, 1/(T |log(x/n)|))` go to `0`, and the series is dominated uniformly for `T ≥ 0` by the
summable sequence `|λ(n)| n^{-(1+β)} = O(n^{-(1+β/2)})`, the estimate
`|λ(n)| ≤ d(n) ≪ n^{β/2}` being the only arithmetic input.

This is Tannery's theorem (`tendsto_tsum_of_dominated_convergence`).
-/
import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs
import Submission.Work.LinnikAreas.perron_triangle_error_decay

namespace Work.LinnikAreas

open DirichletCharacter
open scoped BigOperators

noncomputable section

theorem perrErr_tendsto_zero {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ2 : ψ ^ 2 = 1)
    {β x : ℝ} (hβ : 0 < β) (hx : 0 < x) (hxnn : ∀ n : ℕ, (n : ℝ) ≠ x) :
    Filter.Tendsto (fun T : ℝ => Work.LinnikAreas.perrErr ψ β x T) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (β/2) (by linarith)
  set f : ℝ → ℕ → ℝ := fun T k =>
      Work.LinnikAreas.lamR ψ k * (k : ℝ) ^ (-(1 + β))
        * min 1 (1 / (T * |Real.log (x / (k : ℝ))|)) with hf
  set bound : ℕ → ℝ := fun n => |Work.LinnikAreas.lamR ψ n| * (n : ℝ) ^ (-(1 + β)) with hbnd
  -- The dominating sequence `|λ(n)| n^{-(1+β)}` is summable: `|λ(n)| ≤ d(n) ≪ n^{β/2}`.
  have hsumm : Summable bound := by
    have hg : Summable (fun n : ℕ => C * (n : ℝ) ^ (-(1 + β/2))) := by
      have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + β/2))) := by
        rw [Real.summable_nat_rpow]; linarith
      exact hs.mul_left C
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hg
    · rw [hbnd]; simp only []
      exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · rw [hbnd]; simp only []
      rcases eq_or_ne n 0 with rfl | hn
      · have hz : Work.LinnikAreas.lamR ψ 0 = 0 := by
          simp [Work.LinnikAreas.lamR, Work.LinnikAreas.lam]
        rw [hz, abs_zero, zero_mul]
        exact mul_nonneg hCpos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have h1 : |Work.LinnikAreas.lamR ψ n| ≤ C * (n : ℝ) ^ (β/2) :=
          le_trans (Work.LinnikAreas.abs_lamR_le_card_divisors ψ n) (hC n)
        have h2 : (n : ℝ) ^ (β/2) * (n : ℝ) ^ (-(1 + β)) = (n : ℝ) ^ (-(1 + β/2)) := by
          rw [← Real.rpow_add hnpos]; congr 1; ring
        calc |Work.LinnikAreas.lamR ψ n| * (n : ℝ) ^ (-(1 + β))
            ≤ (C * (n : ℝ) ^ (β/2)) * (n : ℝ) ^ (-(1 + β)) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ = C * ((n : ℝ) ^ (β/2) * (n : ℝ) ^ (-(1 + β))) := by ring
          _ = C * (n : ℝ) ^ (-(1 + β/2)) := by rw [h2]
  -- Each summand tends to `0`.
  have hpt : ∀ k : ℕ, Filter.Tendsto (fun T : ℝ => f T k) Filter.atTop (nhds 0) := by
    intro k
    have hmain : Filter.Tendsto (fun T : ℝ => min 1 (1 / (T * |Real.log (x / (k : ℝ))|)))
        Filter.atTop (nhds 0) := by
      rcases eq_or_ne |Real.log (x / (k : ℝ))| 0 with h0 | h0
      · have hconst : (fun T : ℝ => min 1 (1 / (T * |Real.log (x / (k : ℝ))|)))
            = fun _ => (0 : ℝ) := by
          funext T
          rw [h0, mul_zero, div_zero]
          exact min_eq_right zero_le_one
        rw [hconst]; exact tendsto_const_nhds
      · have hpos : 0 < |Real.log (x / (k : ℝ))| :=
          lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
        have h1 : Filter.Tendsto (fun T : ℝ => T * |Real.log (x / (k : ℝ))|)
            Filter.atTop Filter.atTop := Filter.tendsto_id.atTop_mul_const hpos
        have h2 : Filter.Tendsto (fun T : ℝ => (T * |Real.log (x / (k : ℝ))|)⁻¹)
            Filter.atTop (nhds 0) := h1.inv_tendsto_atTop
        simpa [one_div, min_eq_right zero_le_one] using
          (tendsto_const_nhds (x := (1 : ℝ))).min h2
    have := hmain.const_mul (Work.LinnikAreas.lamR ψ k * (k : ℝ) ^ (-(1 + β)))
    simpa [hf] using this
  -- Uniform domination for `T ≥ 0`.
  have hbound : ∀ᶠ T in Filter.atTop, ∀ k : ℕ, ‖f T k‖ ≤ bound k := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    intro k
    have hc : 0 ≤ 1 / (T * |Real.log (x / (k : ℝ))|) :=
      div_nonneg zero_le_one (mul_nonneg hT (abs_nonneg _))
    have hmin : |min 1 (1 / (T * |Real.log (x / (k : ℝ))|))| ≤ 1 := by
      rw [abs_of_nonneg (le_min zero_le_one hc)]
      exact min_le_left _ _
    have hnorm : ‖f T k‖ = |Work.LinnikAreas.lamR ψ k| * (k : ℝ) ^ (-(1 + β))
        * |min 1 (1 / (T * |Real.log (x / (k : ℝ))|))| := by
      rw [hf]; simp only []
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
    rw [hnorm, hbnd]; simp only []
    exact mul_le_of_le_one_right
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)) hmin
  -- Tannery.
  have hres := tendsto_tsum_of_dominated_convergence hsumm hpt hbound
  simpa [hf, Work.LinnikAreas.perrErr] using hres

end

end Work.LinnikAreas
