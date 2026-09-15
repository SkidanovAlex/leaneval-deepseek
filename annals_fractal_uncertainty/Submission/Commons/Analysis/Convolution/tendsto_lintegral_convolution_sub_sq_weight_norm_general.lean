import Mathlib
import Submission.Commons.Analysis.Convolution.tendsto_lintegral_convolution_sub_sq_fin_vec

namespace Commons.Analysis.Convolution

open MeasureTheory Filter
open scoped Topology ENNReal

/-- **Weighted `L²`-convergence of mollification, arbitrary continuous weight.**

For an `L²` function `u : ℂᵈ → E` (with `E` a complete real normed space) of compact support,
convolving against a family of nonnegative approximate identities `ρ i` (total mass `1`, supported
in balls of radius `R i → 0`) and weighting the squared defect by any continuous nonnegative
function `Φ` gives convergence to `0` of the weighted `L²`-norm of the defect.

Unlike `tendsto_lintegral_convolution_sub_sq_weight_norm_complete`, no compact support of `Φ` is
required: the defect is supported in a fixed compact set (the support of `u` thickened by radius
`1`), on which `Φ` is bounded. -/
theorem tendsto_lintegral_convolution_sub_sq_weight_norm_general {d : ℕ} {ι : Type*} {l : Filter ι}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Φ : (Fin d → ℂ) → ℝ) (hΦc : Continuous Φ) (hΦnn : ∀ x, 0 ≤ Φ x)
    (ρ : ι → (Fin d → ℂ) → ℝ) (hρnn : ∀ i x, 0 ≤ ρ i x)
    (hρi : ∀ i, MeasureTheory.Integrable (ρ i) (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hρ1 : ∀ i, ∫ x, ρ i x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 1)
    (R : ι → ℝ) (hRpos : ∀ i, 0 ≤ R i) (hR : Filter.Tendsto R l (nhds 0))
    (hRs : ∀ i, ∀ x, R i < ‖x‖ → ρ i x = 0)
    (u : (Fin d → ℂ) → E) (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hus : HasCompactSupport u) :
    Filter.Tendsto (fun i => ∫⁻ x, ENNReal.ofReal
      (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2 * Φ x)
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) l (nhds 0) := by
  classical
  -- Step 1: a norm bound `M₁` for the support of `u`.
  obtain ⟨M₀, hM₀⟩ : ∃ M : ℝ, ∀ x, u x ≠ 0 → ‖x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hus.isCompact.isBounded.exists_norm_le
    exact ⟨M, fun x hx => hM x (subset_tsupport u (Function.mem_support.mpr hx))⟩
  set M₁ : ℝ := max M₀ 0 with hM₁def
  have hM₀le : M₀ ≤ M₁ := le_max_left _ _
  have hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ M₁ := fun x hx => le_trans (hM₀ x hx) hM₀le
  -- Step 2: a bound `C` for `Φ` on the ball `closedBall 0 (M₁ + 1)`.
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_closedBall (0 : Fin d → ℂ) (M₁ + 1)).exists_bound_of_continuousOn hΦc.continuousOn
  set C : ℝ := max C₀ 0 with hCdef
  have hCnn : 0 ≤ C := le_max_right _ _
  have hΦle : ∀ x, ‖x‖ ≤ M₁ + 1 → Φ x ≤ C := by
    intro x hx
    have hxmem : x ∈ Metric.closedBall (0 : Fin d → ℂ) (M₁ + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx
    have h := hC₀ x hxmem
    rw [Real.norm_of_nonneg (hΦnn x)] at h
    exact le_trans h (le_max_left _ _)
  -- Step 3: pointwise bound of the weighted defect by `C` times the unweighted defect.
  have key : ∀ i, R i ≤ 1 →
      (∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2 * Φ x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
      ≤ ENNReal.ofReal C * (∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) := by
    intro i hRi
    have hpt : ∀ x, ENNReal.ofReal
          (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2 * Φ x)
        ≤ ENNReal.ofReal
            (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2)
          * ENNReal.ofReal C := by
      intro x
      by_cases hx : ‖x‖ ≤ M₁ + 1
      · rw [ENNReal.ofReal_mul (sq_nonneg _)]
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hΦle x hx))
      · push Not at hx
        have hux : u x = 0 := by
          by_contra hne
          exact absurd (hsupp x hne) (not_le.mpr (by linarith))
        have hconv : (∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) = 0 := by
          have hzero : (fun y => ρ i y • u (x - y)) = fun _ => (0 : E) := by
            funext y
            by_cases hρy : ρ i y = 0
            · rw [hρy, zero_smul]
            · have hyR : ‖y‖ ≤ R i := by
                by_contra hcon
                exact hρy (hRs i y (lt_of_not_ge hcon))
              have huxy : u (x - y) = 0 := by
                by_contra hne
                have h1 : ‖x - y‖ ≤ M₁ := hsupp _ hne
                have h2 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
                  calc ‖x‖ = ‖(x - y) + y‖ := by ring_nf
                    _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
                have hy1 : ‖y‖ ≤ 1 := le_trans hyR hRi
                linarith
              rw [huxy, smul_zero]
          rw [hzero]; simp
        rw [hconv, hux, sub_zero, norm_zero]
        simp
    calc (∫⁻ x, ENNReal.ofReal
            (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2 * Φ x)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
        ≤ ∫⁻ x, ENNReal.ofReal
            (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2)
          * ENNReal.ofReal C ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
          lintegral_mono hpt
      _ = (∫⁻ x, ENNReal.ofReal
            (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) * ENNReal.ofReal C := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal C * (∫⁻ x, ENNReal.ofReal
            (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) := by
          rw [mul_comm]
  -- Step 4: unweighted `L²`-convergence of the mollification.
  have hbase := tendsto_lintegral_convolution_sub_sq_fin_vec ρ hρnn hρi hρ1 R hRpos hR hRs u hu
  have hlim : Filter.Tendsto (fun i => ENNReal.ofReal C * (∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) - u x‖ ^ 2)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))) l (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hbase (Or.inr ENNReal.ofReal_ne_top)
  -- Step 5: squeeze.
  have hRle1 : ∀ᶠ i in l, R i ≤ 1 :=
    hR.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  rw [ENNReal.tendsto_nhds_zero] at hlim ⊢
  intro ε hε
  filter_upwards [hlim ε hε, hRle1] with i hi hRi
  exact le_trans (key i hRi) hi

end Commons.Analysis.Convolution
