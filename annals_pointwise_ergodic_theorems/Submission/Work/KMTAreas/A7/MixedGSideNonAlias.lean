/-
# The repaired-window non-aliasing (and separation) of the mixed range (Area A7)

For the fibre (`form-1`/sampling) estimate of the mixed range one needs, on the *repaired* window
`u₀ = loMixedU ρ d l₂ k₁ k₂`, that the arithmetic frequencies `(ℚ/ℤ)_{≤ l₂}` are `2^{-2u₀}`-separated.
The repaired window dominates the frozen window of the large-scale analysis
(`uScale ρ L ≤ loMixedU`, `L = Lnat 0 l₂ k₁ k₂`), so the non-aliasing statement
`exists_nonAliasing_uScale` (proved, for `L` above a `ρ`-dependent threshold) transfers to `u₀`
by monotonicity of `NonAliasing` in the scale and in the frequency set.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.MixedGSideAux
import Submission.Work.KMTAreas.A7.fiberVarSamplingReduce
import Submission.Work.KMTAreas.A7.collapse

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- `ℝ_{≤k} ⊆ ℝ_{≤k'}` for `k ≤ k'`. -/
theorem realArc_mono {k k' : ℤ} (hk : k ≤ k') : realArc k ⊆ realArc k' := by
  intro θ hθ
  rw [realArc] at hθ ⊢
  obtain ⟨h1, h2⟩ := hθ
  have hz : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k' := zpow_le_zpow_right₀ (by norm_num) hk
  exact ⟨by linarith, le_trans h2 hz⟩

/-- Non-aliasing at a larger scale implies non-aliasing at a smaller one. -/
theorem NonAliasing_mono_scale {k k' : ℤ} (hk : k ≤ k') {A : Finset Work.Analysis.IonescuWainger.Circle}
    (h : NonAliasing k' A) : NonAliasing k A := by
  intro α hα β hβ θ hθ θ' hθ' heq
  exact h α hα β hβ θ (realArc_mono hk hθ) θ' (realArc_mono hk hθ') heq

/-- **Non-aliasing of the arithmetic frequencies at the repaired window.**  Above a
`ρ`-dependent threshold for `L = Lnat 0 l₂ k₁ k₂`, the set `(ℚ/ℤ)_{≤ l₂}` is non-aliasing at the
scale `-(2 · loMixedU ρ d l₂ k₁ k₂)`. -/
theorem NonAliasing_loMixedU (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℕ) :
    ∃ B : ℕ, ∀ (l₂ k₁ k₂ : ℕ), B ≤ Lnat 0 l₂ k₁ k₂ →
      NonAliasing (-(2 * (loMixedU ρ d l₂ k₁ k₂ : ℤ))) (iwArithFreqs ρ l₂) := by
  obtain ⟨B, hB⟩ := exists_nonAliasing_uScale ρ hρ hρ1
  refine ⟨B, fun l₂ k₁ k₂ hBL => ?_⟩
  have hl₂L : l₂ ≤ Lnat 0 l₂ k₁ k₂ :=
    le_trans (le_trans (le_max_right 0 l₂) (le_max_left (max 0 l₂) (max k₁ k₂)))
      (le_of_eq rfl)
  have h1 : NonAliasing (-(2 * (uScale ρ (Lnat 0 l₂ k₁ k₂) : ℤ))) (iwArithFreqs ρ l₂) :=
    hB l₂ (Lnat 0 l₂ k₁ k₂) hl₂L hBL
  have hle : uScale ρ (Lnat 0 l₂ k₁ k₂) ≤ loMixedU ρ d l₂ k₁ k₂ :=
    uScale_le_loMixedU ρ d l₂ k₁ k₂
  have h2 : (-(2 * (loMixedU ρ d l₂ k₁ k₂ : ℤ))) ≤
      (-(2 * (uScale ρ (Lnat 0 l₂ k₁ k₂) : ℤ))) := by
    have : (2 * (uScale ρ (Lnat 0 l₂ k₁ k₂) : ℤ)) ≤ 2 * (loMixedU ρ d l₂ k₁ k₂ : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by norm_num)
    omega
  exact NonAliasing_mono_scale h2 h1

end

end Work.KMTAreas.A7
