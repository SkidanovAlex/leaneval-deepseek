import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PhiStar.Honesty.sq_integral_sqrt_mul_le
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- **Weighted Cauchy–Schwarz for the `cos θ dθ` pairing.**  For functions `g`, `e` whose
squares are integrable against `cos θ` on `Iθ = Set.Icc 0 (Real.pi/2)`, and with the pairing
integral `θ ↦ g θ * e θ * cos θ` itself integrable,

  `(∫_{Iθ} g θ * e θ * cos θ)² ≤ (∫_{Iθ} (g θ)² cos θ) · (∫_{Iθ} (e θ)² cos θ)`.

*Route (for the prover).*  On `Iθ` one has `Real.cos θ ≥ 0`, so the pointwise identity
`Real.sqrt ((g θ)² cos θ) * Real.sqrt ((e θ)² cos θ) = |g θ| * |e θ| * cos θ` holds
(`Real.sqrt_mul`, `Real.sqrt_sq_eq_abs`, `Real.sq_sqrt`).  `Work.PhiStar.Honesty.sq_integral_sqrt_mul_le`
(with `A := fun θ => (g θ)² cos θ`, `B := fun θ => (e θ)² cos θ`, both nonnegative on `Iθ` and
integrable by hypothesis) gives `(∫ √A √B)² ≤ (∫ A)(∫ B)`; convert `∫ √A √B` into
`∫ |g θ| |e θ| cos θ` with `MeasureTheory.setIntegral_congr_fun measurableSet_Icc`, and finish
with `|∫ g θ e θ cos θ| ≤ ∫ |g θ e θ cos θ| = ∫ |g θ| |e θ| cos θ`
(`MeasureTheory.abs_integral_le_integral_abs` + `MeasureTheory.setIntegral_congr_fun` using
`cos θ ≥ 0`). -/
theorem sq_integral_mul_cos_le (g e : ℝ → ℝ)
    (hg : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (he : MeasureTheory.IntegrableOn (fun θ : ℝ => (e θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hge : MeasureTheory.IntegrableOn (fun θ : ℝ => g θ * e θ * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, g θ * e θ * Real.cos θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.cos θ)
        * (∫ θ in Work.Spaces.Iθ, (e θ) ^ 2 * Real.cos θ) := by
  -- `cos` is nonnegative on `Iθ = [0, π/2]`.
  have hcn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.cos θ := by
    intro θ hθ
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hAnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (g θ) ^ 2 * Real.cos θ :=
    fun θ hθ => mul_nonneg (sq_nonneg _) (hcn θ hθ)
  have hBnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (e θ) ^ 2 * Real.cos θ :=
    fun θ hθ => mul_nonneg (sq_nonneg _) (hcn θ hθ)
  -- Bunyakovsky for the square roots.
  have hcs := Work.PhiStar.Honesty.sq_integral_sqrt_mul_le measurableSet_Icc hg he hAnn hBnn
  -- On `Iθ`, `√((g θ)² cos θ) · √((e θ)² cos θ) = |g θ| |e θ| cos θ`.
  have hsqrt : ∀ θ ∈ Work.Spaces.Iθ,
      Real.sqrt ((g θ) ^ 2 * Real.cos θ) * Real.sqrt ((e θ) ^ 2 * Real.cos θ)
        = |g θ| * |e θ| * Real.cos θ := by
    intro θ hθ
    have hc := hcn θ hθ
    have hs : Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ) = Real.cos θ := by
      rw [← sq, Real.sq_sqrt hc]
    rw [Real.sqrt_mul (sq_nonneg (g θ)) (Real.cos θ),
        Real.sqrt_mul (sq_nonneg (e θ)) (Real.cos θ),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    calc |g θ| * Real.sqrt (Real.cos θ) * (|e θ| * Real.sqrt (Real.cos θ))
        = |g θ| * |e θ| * (Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ)) := by ring
      _ = |g θ| * |e θ| * Real.cos θ := by rw [hs]
  have habs1 : ∀ θ ∈ Work.Spaces.Iθ, |g θ| * |e θ| * Real.cos θ = |g θ * e θ * Real.cos θ| := by
    intro θ hθ
    rw [abs_mul, abs_mul, abs_of_nonneg (hcn θ hθ)]
  have habs : ∫ θ in Work.Spaces.Iθ, Real.sqrt ((g θ) ^ 2 * Real.cos θ) * Real.sqrt ((e θ) ^ 2 * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, |g θ * e θ * Real.cos θ| :=
    (MeasureTheory.setIntegral_congr_fun measurableSet_Icc hsqrt).trans
      (MeasureTheory.setIntegral_congr_fun measurableSet_Icc habs1)
  -- `|∫ g e cos| ≤ ∫ |g e cos|`.
  have hkey : |(∫ θ in Work.Spaces.Iθ, g θ * e θ * Real.cos θ)|
      ≤ ∫ θ in Work.Spaces.Iθ, |g θ * e θ * Real.cos θ| := by
    have := MeasureTheory.abs_integral_le_integral_abs
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (f := fun θ => g θ * e θ * Real.cos θ)
    simpa using this
  have step1 : (∫ θ in Work.Spaces.Iθ, g θ * e θ * Real.cos θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, |g θ * e θ * Real.cos θ|) ^ 2 := by
    have h := mul_self_le_mul_self
      (abs_nonneg (∫ θ in Work.Spaces.Iθ, g θ * e θ * Real.cos θ)) hkey
    simpa [← sq, sq_abs] using h
  calc (∫ θ in Work.Spaces.Iθ, g θ * e θ * Real.cos θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, |g θ * e θ * Real.cos θ|) ^ 2 := step1
    _ = (∫ θ in Work.Spaces.Iθ,
          Real.sqrt ((g θ) ^ 2 * Real.cos θ) * Real.sqrt ((e θ) ^ 2 * Real.cos θ)) ^ 2 := by
        rw [habs]
    _ ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.cos θ)
          * (∫ θ in Work.Spaces.Iθ, (e θ) ^ 2 * Real.cos θ) := hcs

end Work.FTS.PhiStar.Honesty
