import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set

/-- Over the angular interval `Iθ = [0,π/2]`, whose length is `π/2`, the mean of a
continuous function is at least its minimum.  Concretely: a continuous `φ` attains
its minimum on the compact set `Iθ`, and the average `(2/π) ∫_{Iθ} φ` dominates that
minimum because `∫_{Iθ} φ ≥ (π/2) · min`. -/
theorem MinLeAvg {φ : ℝ → ℝ} (hφ : ContinuousOn φ Work.Spaces.Iθ) :
    ∃ θ₀ ∈ Work.Spaces.Iθ, φ θ₀ ≤ (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
  have hIcc : Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) := rfl
  have hK : IsCompact Work.Spaces.Iθ := by rw [hIcc]; exact isCompact_Icc
  have hne : (Work.Spaces.Iθ).Nonempty :=
    ⟨0, by rw [hIcc]; exact ⟨le_refl 0, by positivity⟩⟩
  obtain ⟨θ₀, hθ₀, hmin⟩ := hK.exists_isMinOn hne hφ
  have hint : IntegrableOn φ Work.Spaces.Iθ := ContinuousOn.integrableOn_compact hK hφ
  have hμ : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [hIcc]; exact (isCompact_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).measure_lt_top.ne
  have hcint : IntegrableOn (fun _ : ℝ => φ θ₀) Work.Spaces.Iθ :=
    integrableOn_const (μ := volume) hμ (by simp)
  have hmono : ∫ θ in Work.Spaces.Iθ, (φ θ₀) ≤ ∫ θ in Work.Spaces.Iθ, φ θ :=
    setIntegral_mono_on hcint hint (by rw [hIcc]; exact measurableSet_Icc)
      (fun θ hθ => hmin hθ)
  have hconst : ∫ θ in Work.Spaces.Iθ, (φ θ₀) = φ θ₀ * (Real.pi / 2) := by
    rw [setIntegral_const, hIcc, MeasureTheory.Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  refine ⟨θ₀, hθ₀, ?_⟩
  have h1 : φ θ₀ * (Real.pi / 2) ≤ ∫ θ in Work.Spaces.Iθ, φ θ := hconst ▸ hmono
  have h2 : (0 : ℝ) < 2 / Real.pi := by positivity
  have h3 : (2 / Real.pi) * (φ θ₀ * (Real.pi / 2)) = φ θ₀ := by field_simp
  calc φ θ₀ = (2 / Real.pi) * (φ θ₀ * (Real.pi / 2)) := h3.symm
    _ ≤ (2 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ :=
        mul_le_mul_of_nonneg_left h1 h2.le

end Work.FTS.H2
