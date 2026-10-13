import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.integral_sin_two_neg_rpow_le
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary

/-- Both exponents occurring in the block integrals are of the form `-q` with `0 < q < 1`, so
`Work.Coercivity.integral_sin_two_neg_rpow_le` applies directly:

* `eta - 2α/3 = 97/300 + (1-α)2/3 ≥ 97/300 > 0` for `α ≤ 1`, giving the bound
  `4/(1 - (eta - 2α/3)) = 4/(1/100 + 2α/3) ≤ 400`;
* `gam α - 2α/3 = 1 - 17α/30 ∈ [13/30, 1)` for `0 < α ≤ 1`, and
  `4/(1 - (gam α - 2α/3)) = 4/(17α/30) = 120/(17α)` **exactly**. -/
theorem sin_two_rpow_block_integrals : ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta))
        Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)) ≤ 400 ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      ≤ 120 / (17 * α) := by
  intro α hα
  obtain ⟨hα0, hα1⟩ := hα
  have heta : Work.Spaces.eta = 99 / 100 := rfl
  have hgam : Work.Spaces.gam α = 1 + α / 10 := rfl
  -- ### The first block: exponent `2α/3 - η = -(η - 2α/3)`
  have hq0 : 0 < Work.Spaces.eta - 2 * α / 3 := by
    rw [heta]; linarith
  have hq1 : Work.Spaces.eta - 2 * α / 3 < 1 := by
    rw [heta]; linarith
  obtain ⟨hInt1, hBd1⟩ :=
    Work.Coercivity.integral_sin_two_neg_rpow_le (Work.Spaces.eta - 2 * α / 3) hq0 hq1
  have hexp1 : (2 * α / 3 : ℝ) - Work.Spaces.eta = -(Work.Spaces.eta - 2 * α / 3) := by ring
  -- ### The second block: exponent `2α/3 - γ = -(γ - 2α/3)`
  have hq0' : 0 < Work.Spaces.gam α - 2 * α / 3 := by
    rw [hgam]; linarith
  have hq1' : Work.Spaces.gam α - 2 * α / 3 < 1 := by
    rw [hgam]; linarith
  obtain ⟨hInt2, hBd2⟩ :=
    Work.Coercivity.integral_sin_two_neg_rpow_le (Work.Spaces.gam α - 2 * α / 3) hq0' hq1'
  have hexp2 : (2 * α / 3 : ℝ) - Work.Spaces.gam α = -(Work.Spaces.gam α - 2 * α / 3) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hexp1] using hInt1
  · have h400 : 4 / (1 - (99 / 100 - 2 * α / 3)) ≤ 400 := by
      rw [show (1 : ℝ) - (99 / 100 - 2 * α / 3) = 1 / 100 + 2 * α / 3 by ring]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 / 100 + 2 * α / 3)]
      linarith
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta - 2 * α / 3)) := by
          simp only [hexp1]
      _ ≤ 4 / (1 - (Work.Spaces.eta - 2 * α / 3)) := hBd1
      _ = 4 / (1 - (99 / 100 - 2 * α / 3)) := by rw [heta]
      _ ≤ 400 := h400
  · simpa only [hexp2] using hInt2
  · have hb2 : 4 / (1 - (Work.Spaces.gam α - 2 * α / 3)) = 120 / (17 * α) := by
      rw [show (1 : ℝ) - (Work.Spaces.gam α - 2 * α / 3) = 17 * α / 30 by rw [hgam]; ring]
      rw [div_eq_div_iff (by positivity : (17 * α / 30 : ℝ) ≠ 0)
        (by positivity : (17 * α : ℝ) ≠ 0)]
      ring
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)
        = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 2 * α / 3)) := by
          simp only [hexp2]
      _ ≤ 4 / (1 - (Work.Spaces.gam α - 2 * α / 3)) := hBd2
      _ = 120 / (17 * α) := hb2

end Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary
