import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_log_region
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_compact_width

namespace Commons.NumberTheory.Zeta

/-!
# The zero-free region of `ζ` in `log` form, valid at ALL heights

The commons already has the zero-free region at large height in the form
`1 - c/log(|t|+3) ≤ σ` (`Commons.NumberTheory.Zeta.zeta_zeroFree_log_region`,
`Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight`) and near the axis, `|t| ≤ 4`, with a
single constant (`Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis`).  This claim packages the two
into the log-form region valid for every height:

`ζ(σ + i t) ≠ 0` whenever `1 - c / log(|t| + 2) ≤ σ ≤ 2`.

The middle range `4 ≤ |t| ≤ H` (a fixed compact rectangle) is handled by
`Commons.NumberTheory.Zeta.zeta_zeroFree_compact_width`, obtained by compactness of the zero set.
-/
open Complex MeasureTheory Filter Set
open scoped Topology

/-- Zero-free region of `ζ` in log form at all heights. -/
theorem zeta_ne_zero_log_zeroFree :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ,
      1 - c / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  -- Ingredients: near the axis, in a fixed compact rectangle, and at large height.
  obtain ⟨ε₀, hε₀, hnear⟩ := zeta_zeroFree_near_axis
  obtain ⟨c₀, T₀, hc₀, hT₀, hlarge⟩ := zeta_zeroFreeRegion_largeHeight
  let H : ℝ := max T₀ 4
  have hH4 : (4 : ℝ) ≤ H := le_max_right T₀ 4
  obtain ⟨ε, hε, hcomp⟩ := zeta_zeroFree_compact_width H hH4
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- The constant is the minimum of the three widths, normalised so that
  -- `log 2 ≤ log(|t|+2)` and `log(|t|+3) ≤ 2 log(|t|+2)` do the rest.
  refine ⟨min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2),
    lt_min (lt_min (mul_pos hε₀ hlog2pos) (mul_pos hε hlog2pos)) (by linarith), ?_⟩
  intro σ t hσ hσ2
  -- Convert to the argument shape used by the commons lemmas.
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by ring
  -- The three bounds on `c` that we will use.
  have hc1 : min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2) ≤ ε₀ * Real.log 2 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hc2 : min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2) ≤ ε * Real.log 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hc3 : min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2) ≤ c₀ / 2 :=
    min_le_right _ _
  -- `log 2 ≤ log(|t|+2)`.
  have hlog2le : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog12pos : 0 < Real.log (|t| + 2) := lt_of_lt_of_le hlog2pos hlog2le
  rw [harg]
  by_cases hsmall : |t| ≤ 4
  · -- Near the axis: `1 - ε₀ ≤ σ`.
    have hdiv : min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2) / Real.log (|t| + 2) ≤ ε₀ := by
      rw [div_le_iff₀ hlog12pos]
      calc min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2)
          ≤ ε₀ * Real.log 2 := hc1
        _ ≤ ε₀ * Real.log (|t| + 2) := mul_le_mul_of_nonneg_left hlog2le (le_of_lt hε₀)
    exact hnear t σ hsmall (by linarith) hσ2
  · by_cases hlarge_t : H ≤ |t|
    · -- Large height: `1 - c₀/log(|t|+3) ≤ σ`, using `log(|t|+3) ≤ 2 log(|t|+2)`.
      have hTt : T₀ ≤ |t| := le_trans (le_max_left T₀ 4) hlarge_t
      have hlog3le : Real.log (|t| + 3) ≤ 2 * Real.log (|t| + 2) := by
        have hsq : Real.log (|t| + 3) ≤ Real.log ((|t| + 2) ^ 2) :=
          Real.log_le_log (by linarith [abs_nonneg t]) (by nlinarith [abs_nonneg t])
        rwa [Real.log_pow] at hsq
      have hlog3pos : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith [abs_nonneg t])
      have hdiv : min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2) / Real.log (|t| + 2)
          ≤ c₀ / Real.log (|t| + 3) := by
        rw [div_le_div_iff₀ hlog12pos hlog3pos]
        calc min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2) * Real.log (|t| + 3)
            ≤ (c₀ / 2) * (2 * Real.log (|t| + 2)) :=
              mul_le_mul hc3 hlog3le (le_of_lt hlog3pos) (by linarith)
          _ = c₀ * Real.log (|t| + 2) := by ring
      have hσ' : 1 - c₀ / Real.log (|t| + 3) ≤ σ := by linarith
      exact hlarge t hTt σ hσ'
    · -- Middle range `4 ≤ |t| ≤ H`: compact rectangle, `1 - ε ≤ σ`.
      have hHt : |t| ≤ H := le_of_lt (lt_of_not_ge hlarge_t)
      have hdiv : min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2) / Real.log (|t| + 2) ≤ ε := by
        rw [div_le_iff₀ hlog12pos]
        calc min (min (ε₀ * Real.log 2) (ε * Real.log 2)) (c₀ / 2)
            ≤ ε * Real.log 2 := hc2
          _ ≤ ε * Real.log (|t| + 2) := mul_le_mul_of_nonneg_left hlog2le (le_of_lt hε)
      exact hcomp t σ hHt (by linarith) hσ2

end Commons.NumberTheory.Zeta
