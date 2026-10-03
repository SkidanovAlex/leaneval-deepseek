import Mathlib
import Submission.Work.A3.integral_min_one_rpow_le
import Submission.Work.A3.min_rpow_eq

namespace Work.A3

open MeasureTheory

/-- **The `β`-integral bound behind the A3 major-arc estimate.**

For `C > 0` and `d ≥ 2` there is `K = K(C,d) > 0` with
`∫_ℝ (min (N) (C |β|^{-1/d}))^{2s} dβ ≤ K^{2s} N^{2s-d}` for all `N ≥ 1` and all `s`
satisfying `d < 2s` — the constant being *uniform* in `s`, which is the point of the lemma.

The integrand is symmetric in `β`, so it suffices to bound `∫_0^∞`.  The function
`β ↦ min (N) (C β^{-1/d})` equals `N` on `(0, (C/N)^d]` and `C β^{-1/d}` afterwards; after
the change of variables `β = ((C/N)^d) γ` the whole integral reduces to the single model
integral `∫_ℝ (min 1 |γ|^{-1/d})^{2s} dγ`, which is at most `2 (1 + d)` because
`(2s)/d > 1 + 1/d` (`d < 2s` with `d, s` integers).  Concretely

`∫_ℝ (min (N) (C|β|^{-1/d}))^{2s} dβ = N^{2s} ((C/N)^d) ∫_ℝ (min 1 |γ|^{-1/d})^{2s} dγ
   ≤ 2 (1+d) C^d N^{2s-d}`,

so one may take `K = max 1 (2(1+d) C^d)`; indeed `K^{2s} ≥ K ≥ 2(1+d) C^d` as `2s ≥ 1`. -/
theorem min_rpow_integral_bound (C : ℝ) (hC : 0 < C) (d : ℕ) (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N s : ℕ), 1 ≤ N → d < 2 * s →
      ∫ β : ℝ, (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)
        ≤ K ^ (2 * s) * (N : ℝ) ^ (2 * s - d) := by
  refine ⟨max 1 (2 * (1 + (d : ℝ)) * C ^ d), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro N s hN hs
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hapos : 0 < ((C : ℝ) / (N : ℝ)) ^ d := by positivity
    -- the model integral `∫ (min 1 |γ|^{-1/d})^{2s}`
    have hg := integral_min_one_rpow_le d s hd hs
    -- `h1`: pointwise identification of the integrand
    have h1 : (∫ β : ℝ, (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s))
        = ∫ β : ℝ, (N : ℝ) ^ (2 * s) *
            (min 1 (|(((C : ℝ) / (N : ℝ)) ^ d)⁻¹ * β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with β
      exact min_rpow_eq C hC d s N (by omega) hN β
    -- `h2`: pull the constant `N^{2s}` out of the integral
    have h2 : (∫ β : ℝ, (N : ℝ) ^ (2 * s) *
            (min 1 (|(((C : ℝ) / (N : ℝ)) ^ d)⁻¹ * β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s))
        = (N : ℝ) ^ (2 * s) * ∫ β : ℝ,
            (min 1 (|(((C : ℝ) / (N : ℝ)) ^ d)⁻¹ * β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s) :=
      MeasureTheory.integral_const_mul _ _
    -- `h3`: the rescaling `β = ((C/N)^d) γ` of Lebesgue measure
    have h3 : (∫ β : ℝ,
            (min 1 (|(((C : ℝ) / (N : ℝ)) ^ d)⁻¹ * β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s))
        = ((C : ℝ) / (N : ℝ)) ^ d *
            ∫ γ : ℝ, (min 1 (|γ| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s) := by
      have key := MeasureTheory.Measure.integral_comp_mul_left
        (fun γ : ℝ => (min 1 (|γ| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s))
        (((C : ℝ) / (N : ℝ)) ^ d)⁻¹
      simpa [smul_eq_mul, inv_inv, abs_of_pos hapos] using key
    have harith : (N : ℝ) ^ (2 * s) * (((C : ℝ) / (N : ℝ)) ^ d * (2 * (1 + (d : ℝ))))
        = 2 * (1 + (d : ℝ)) * C ^ d * (N : ℝ) ^ (2 * s - d) := by
      rw [div_pow, pow_sub₀ (N : ℝ) hNpos.ne' (le_of_lt hs)]
      ring
    calc ∫ β : ℝ, (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)
        = (N : ℝ) ^ (2 * s) * (((C : ℝ) / (N : ℝ)) ^ d *
            ∫ γ : ℝ, (min 1 (|γ| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)) := by rw [h1, h2, h3]
      _ ≤ (N : ℝ) ^ (2 * s) * (((C : ℝ) / (N : ℝ)) ^ d * (2 * (1 + (d : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 2 * (1 + (d : ℝ)) * C ^ d * (N : ℝ) ^ (2 * s - d) := harith
      _ ≤ (max 1 (2 * (1 + (d : ℝ)) * C ^ d)) ^ (2 * s) * (N : ℝ) ^ (2 * s - d) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc 2 * (1 + (d : ℝ)) * C ^ d ≤ max 1 (2 * (1 + (d : ℝ)) * C ^ d) := le_max_right _ _
            _ ≤ (max 1 (2 * (1 + (d : ℝ)) * C ^ d)) ^ (2 * s) :=
                le_self_pow₀ (le_max_left _ _) (by omega)

end Work.A3
