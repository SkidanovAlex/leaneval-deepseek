import Mathlib
import Submission.Work.Holonomy3.model_deps

namespace Work.Holonomy3

open scoped BigOperators

/-- The left-endpoint Riemann sum of a nondecreasing function over an arithmetic grid is at most
the integral over the corresponding range: with grid points `a + j*h` (`h ≥ 0`, `j₀ ≤ d`),
`Σ_{j₀ ≤ j < d} h * f (a + j*h) ≤ ∫_{a + j₀*h}^{a + d*h} f`.
(Each term is at most the integral over the following interval of length `h`.) -/
theorem sum_mul_le_integral_of_monotone {d : ℕ} (hd : 1 ≤ d) {f : ℝ → ℝ} (hf : Monotone f)
    {a h : ℝ} (hh : 0 ≤ h) {j₀ : ℕ} (hj₀ : j₀ ≤ d) :
    ∑ j ∈ Finset.Icc j₀ (d - 1), h * f (a + (j : ℝ) * h)
      ≤ ∫ t in (a + (j₀ : ℝ) * h)..(a + (d : ℝ) * h), f t := by
  -- rewrite the sum over `Icc j₀ (d-1)` as a sum over `Ico j₀ d`
  have hIcc : Finset.Icc j₀ (d - 1) = Finset.Ico j₀ d := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  -- each term is at most the integral over the following interval of length `h`
  have key : ∀ j ∈ Finset.Ico j₀ d,
      h * f (a + (j : ℝ) * h)
        ≤ ∫ t in (a + (j : ℝ) * h)..(a + ((j + 1 : ℕ) : ℝ) * h), f t := by
    intro j _
    have hcast : a + ((j + 1 : ℕ) : ℝ) * h = a + (j : ℝ) * h + h := by push_cast; ring
    rw [hcast]
    have hconst : h * f (a + (j : ℝ) * h)
        = ∫ t in (a + (j : ℝ) * h)..(a + (j : ℝ) * h + h), f (a + (j : ℝ) * h) := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    rw [hconst]
    -- the constant `f (a + j*h)` is dominated by `f` on the slice by monotonicity
    exact intervalIntegral.integral_mono_on (le_add_of_nonneg_right hh) intervalIntegrable_const
      hf.intervalIntegrable fun t ht => hf ht.1
  calc ∑ j ∈ Finset.Ico j₀ d, h * f (a + (j : ℝ) * h)
      ≤ ∑ j ∈ Finset.Ico j₀ d,
          ∫ t in (a + (j : ℝ) * h)..(a + ((j + 1 : ℕ) : ℝ) * h), f t :=
        Finset.sum_le_sum key
    _ = ∫ t in (a + (j₀ : ℝ) * h)..(a + (d : ℝ) * h), f t :=
        intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k => a + (k : ℝ) * h) hj₀
          fun _ _ => hf.intervalIntegrable

end Work.Holonomy3
