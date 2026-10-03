import Mathlib
import Submission.Commons.NumberTheory.Zeta.riemannZeta_residue_uniform_bound

open Complex Filter Metric Asymptotics
open scoped Topology

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- The residue of the Riemann zeta function at `1`, in real form: `σ · ζ(1+σ) → 1` as
`σ → 0⁺`. -/
theorem sigma_mul_zeta_one_add_tendsto_one :
    Filter.Tendsto (fun σ : ℝ => σ * (riemannZeta ((1 : ℂ) + σ)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  obtain ⟨C, hCpos, r, hrpos, hbound⟩ := riemannZeta_residue_uniform_bound
  -- Step 1: the complex function `σ * ζ(1+σ)` tends to `1` along `σ → 0⁺`.
  have hcomplex : Tendsto (fun σ : ℝ => (σ : ℂ) * riemannZeta ((1 : ℂ) + (σ : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    -- The upper comparison function `σ ↦ C * ‖σ‖` tends to `0`.
    have hupper : Tendsto (fun σ : ℝ => C * ‖((σ : ℂ))‖)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      have hc : Continuous (fun σ : ℝ => C * ‖((σ : ℂ))‖) := by fun_prop
      have htend := (hc.tendsto 0).mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
      simpa using htend
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards with σ using norm_nonneg _
    · -- Eventually `‖σ * ζ(1+σ) - 1‖ ≤ C * ‖σ‖` by the uniform residue bound.
      have hr : ∀ᶠ σ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), σ < r :=
        nhdsWithin_le_nhds (Iio_mem_nhds hrpos)
      filter_upwards [self_mem_nhdsWithin, hr] with σ hσpos hσr
      have hσne : ((σ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hσpos.ne'
      have hnorm : ‖((σ : ℂ))‖ ≤ r := by
        rw [norm_real, Real.norm_eq_abs, abs_of_pos hσpos]
        exact le_of_lt hσr
      exact hbound ((σ : ℂ)) hnorm hσne
  -- Step 2: real parts.  `σ * ζ(1+σ)` is real, so its real part is `σ * Re ζ(1+σ)`.
  have hcomplex_re : Tendsto
      (Complex.re ∘ fun σ : ℝ => (σ : ℂ) * riemannZeta ((1 : ℂ) + (σ : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
    simpa using h
  refine hcomplex_re.congr' ?_
  filter_upwards with σ
  simp [Function.comp_apply, Complex.mul_re]

end Commons.NumberTheory.Zeta
