/-
Copyright: work module for the Elgindi finite-time singularity project.

# Cauchy–Schwarz for the angular weight `K`

The paper's angular weight is `K(θ) = 3 sin θ cos²θ` (`Work.Spaces.K`).  On `Iθ = [0,π/2]` it is
nonnegative and bounded by `3`, and `∫_{Iθ} K² ≤ 9 · (π/2) ≤ 25`, so `K ∈ L²(Iθ)` with
`‖K‖_{L²} ≤ 5`.  Cauchy–Schwarz (Hölder with `p = q = 2`) therefore gives, for a nonnegative
`G` with `∫_{Iθ} G² ≤ M`,

  `∫_{Iθ} K θ * G θ ≤ ‖K‖₂ ‖G‖₂ ≤ 5 √M`,

together with the integrability of `K · G` (as a product of two `L²` functions).
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXB

-- the hypothesis `hM : 0 ≤ M` of the requested statement is not needed by the argument below
-- (if `M < 0` then `hL2` forces `G = 0` a.e. and the conclusion is trivial anyway)
set_option linter.unusedVariables false

open scoped Real

/-- `K` is continuous. -/
private lemma continuous_K : Continuous Work.Spaces.K := by
  unfold Work.Spaces.K
  continuity

/-- `K` is nonnegative on `Iθ`. -/
private lemma K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-- `K` is bounded by `3` on `Iθ`. -/
private lemma K_le_three_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h3 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  nlinarith [h1, h2, h3]

/-- Cauchy–Schwarz for the angular weight `K(θ) = 3 sin θ cos²θ`: a nonnegative `G` whose square
has integral at most `M` on `Iθ` satisfies `∫_{Iθ} K θ * G θ ≤ 5 √M`, and `θ ↦ K θ * G θ` is
integrable on `Iθ`. -/
theorem K_mul_sqrt_le_of_L2 {M : ℝ} {G : ℝ → ℝ}
    (hG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hnn : ∀ θ, 0 ≤ G θ)
    (hint : MeasureTheory.IntegrableOn (fun θ => (G θ) ^ 2) Work.Spaces.Iθ)
    (hL2 : (∫ θ in Work.Spaces.Iθ, (G θ) ^ 2) ≤ M) (hM : 0 ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * G θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) ≤ 5 * Real.sqrt M := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_mem hIθ_meas
  -- `K²` is integrable on `Iθ` and has integral at most `9 · (π/2)`
  have hK2_int : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ ^ 2) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact (continuous_K.pow 2).integrableOn_Icc
  have hK2_le : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ ^ 2) ≤ 9 * (π/2) := by
    have h9 : MeasureTheory.IntegrableOn (fun _ : ℝ => (9:ℝ)) Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hae : (fun θ : ℝ => Work.Spaces.K θ ^ 2) ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun _ => (9:ℝ)) := by
      filter_upwards [hmem] with θ hθ
      have h0 := K_nonneg_of_mem_Iθ hθ
      have h1 := K_le_three_of_mem_Iθ hθ
      nlinarith
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (9:ℝ) := MeasureTheory.integral_mono_ae hK2_int h9 hae
      _ = 9 * (π/2) := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Work.Spaces.Iθ,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring
  -- both `K` and `G` lie in `L²(Iθ)`
  have hKmem : MeasureTheory.MemLp (fun θ => Work.Spaces.K θ) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq continuous_K.aestronglyMeasurable).mpr hK2_int
  have hGmem : MeasureTheory.MemLp G 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hG).mpr hint
  have hKnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.K θ) := by
    filter_upwards [hmem] with θ hθ
    exact K_nonneg_of_mem_Iθ hθ
  have hGnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] G :=
    Filter.Eventually.of_forall hnn
  -- Hölder with `p = q = 2`
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hKnn hGnn
    (by simpa using hKmem) (by simpa using hGmem)
  -- `‖K‖₂ ≤ 5`
  have hK5 : Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ ^ 2) ≤ 5 := by
    refine (Real.sqrt_le_sqrt hK2_le).trans ?_
    have h9 : 9 * (π/2) ≤ 25 := by nlinarith [Real.pi_lt_four]
    calc Real.sqrt (9 * (π/2)) ≤ Real.sqrt 25 := Real.sqrt_le_sqrt h9
      _ = 5 := by norm_num
  have hbound : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) ≤ 5 * Real.sqrt M := by
    refine hholder.trans ?_
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
    exact mul_le_mul hK5 (Real.sqrt_le_sqrt hL2) (Real.sqrt_nonneg _) (by norm_num)
  -- integrability of `K * G` (product of two `L²` functions)
  have hmul : MeasureTheory.MemLp (fun θ => Work.Spaces.K θ * G θ) 1
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hKmem.mul hGmem
  exact ⟨MeasureTheory.memLp_one_iff_integrable.mp hmul, hbound⟩

end Work.FTS_RegExport.RXB
