import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.near_indicator

namespace Work.EKLC6Core

open Work.EKLContract

/- **A bump at a compact set of positive mass.**  For a measure `ν` on `SL₃(ℝ)` which is finite
on compacta, and a compact set `K` with `0 < ν K`, there is a compactly supported continuous
function `θ : SL₃(ℝ) → ℝ` with `0 ≤ θ ≤ 1`, `θ = 1` on `K`, and `∫ θ ∂ν > 0`.

The function is produced by Urysohn's lemma in the strengthened form
`exists_continuous_one_zero_of_isCompact_of_isGδ` (a compact set in a metric space is `Gδ`), which
gives `ψ` with `K = ψ ⁻¹' {1}`, a compact support and values in `[0,1]`.  Then `θ ≥ 1_K` pointwise,
so `∫ θ ∂ν ≥ ∫ 1_K ∂ν = (ν K).toReal > 0`, both `θ` and `1_K` being integrable (`θ` is continuous
with compact support and `ν` is finite on compacta). -/
set_option linter.style.haveILetI false in
open MeasureTheory in
theorem rect_mass_bump {ν : MeasureTheory.Measure Work.EKLContract.SL3} {K : Set Work.EKLContract.SL3}
    (hν : IsFiniteMeasureOnCompacts ν) (hK : IsCompact K) (hKpos : 0 < ν K) :
    ∃ θ : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      (∀ y, 0 ≤ θ y) ∧ (∀ y, θ y ≤ 1) ∧ (∀ y ∈ K, θ y = 1) ∧ 0 < ∫ y, θ y ∂ν := by
  haveI := hν
  obtain ⟨ψ, hψ_eq, -, hψ_supp, hψ_range⟩ :=
    exists_continuous_one_zero_of_isCompact_of_isGδ hK (isGδ_of_isCompact hK) isClosed_empty
      (Set.disjoint_empty K)
  refine ⟨⟨ψ, hψ_supp⟩, ?_, ?_, ?_, ?_⟩
  · intro y; exact (hψ_range y).1
  · intro y; exact (hψ_range y).2
  · intro y hy
    have hy' : y ∈ (⇑ψ) ⁻¹' ({1} : Set ℝ) := hψ_eq ▸ hy
    exact hy'
  · have htop : ν K ≠ ⊤ := (IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK).ne
    have hintθ : Integrable
        (fun y : SL3 => (⟨ψ, hψ_supp⟩ : CompactlySupportedContinuousMap SL3 ℝ) y) ν := by
      simpa using ψ.continuous.integrable_of_hasCompactSupport hψ_supp
    have hintK : Integrable (K.indicator fun _ => (1 : ℝ)) ν := by
      rw [integrable_indicator_iff hK.measurableSet]
      exact integrableOn_const (μ := ν) (s := K) (C := (1 : ℝ)) (hs := htop)
    have hle : (K.indicator fun _ => (1 : ℝ)) ≤
        (fun y : SL3 => (⟨ψ, hψ_supp⟩ : CompactlySupportedContinuousMap SL3 ℝ) y) := by
      intro y
      by_cases hy : y ∈ K
      · have h1 : (⟨ψ, hψ_supp⟩ : CompactlySupportedContinuousMap SL3 ℝ) y = 1 := by
          have : y ∈ (⇑ψ) ⁻¹' ({1} : Set ℝ) := hψ_eq ▸ hy
          simpa using this
        simp [Set.indicator_of_mem hy, h1]
      · simp [Set.indicator_of_notMem hy, (hψ_range y).1]
    have hmono_int : ∫ y, (K.indicator fun _ => (1 : ℝ)) y ∂ν
        ≤ ∫ y, (⟨ψ, hψ_supp⟩ : CompactlySupportedContinuousMap SL3 ℝ) y ∂ν :=
      integral_mono hintK hintθ hle
    have hKint : ∫ y, (K.indicator fun _ => (1 : ℝ)) y ∂ν = (ν K).toReal := by
      rw [integral_indicator_const (1 : ℝ) hK.measurableSet, smul_eq_mul, mul_one]
      rfl
    have hKpos' : 0 < ∫ y, (K.indicator fun _ => (1 : ℝ)) y ∂ν := by
      rw [hKint]
      exact ENNReal.toReal_pos hKpos.ne' htop
    linarith

end Work.EKLC6Core
