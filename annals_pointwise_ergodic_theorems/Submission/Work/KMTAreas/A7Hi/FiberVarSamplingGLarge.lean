import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberVarSamplingGLarge_bdd
import Submission.Work.KMTAreas.A7Hi.FiberSliceAlgebra
import Submission.Work.KMTAreas.A7Hi.FiberVarReduce
import Submission.Work.KMTAreas.A7Hi.winRotResidueBoundDec

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The arithmetic inputs at the `g`-side scale `k₂` -/

theorem farey_and_strict_of_large_L_g (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ B : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N →
      B < max (max l₁ l₂) (max k₁ k₂) →
      (8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) ≤ (N : ℝ)) ∧
        k₂ + 2 * Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) + 1
          ≤ (Work.Analysis.EndVar.logN N).toNat := by
  obtain ⟨Bfun, hBfun⟩ := Work.KMTAreas.A7.lmax_le_of_not_farey ρ hρ hρ1
  obtain ⟨L₀, hL₀⟩ := Work.KMTAreas.A7.exists_uScale_ge ρ hρ
  refine ⟨max (Bfun ρ) L₀, ?_⟩
  intro l₁ l₂ k₁ k₂ N hsplit hB
  have hBlt : Bfun ρ < max (max l₁ l₂) (max k₁ k₂) := lt_of_le_of_lt (le_max_left _ _) hB
  have hL₀L : L₀ ≤ max (max l₁ l₂) (max k₁ k₂) :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hB)
  have hk₂L : k₂ ≤ max (max l₁ l₂) (max k₁ k₂) := by omega
  have hmaxeq : max (max (max l₁ l₂) l₂) (max k₂ k₁) = max (max l₁ l₂) (max k₁ k₂) := by omega
  have hsplit' : Work.KMTAreas.A7.splitCut ρ (max (max (max l₁ l₂) l₂) (max k₂ k₁)) < N := by
    rw [hmaxeq]; exact hsplit
  have hfarey : 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) ≤ (N : ℝ) := by
    by_contra hnot
    have hnot' : ¬ ((2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) * 8
        ≤ (N : ℝ)) := by
      intro hc; exact hnot (by linarith [hc])
    have hle := hBfun (max l₁ l₂) l₂ k₂ k₁ N hsplit' hnot'
    rw [hmaxeq] at hle
    omega
  have hu := hL₀ (max (max l₁ l₂) (max k₁ k₂)) hL₀L
  exact ⟨hfarey, Work.KMTAreas.A7.strict_of_splitCut_lt hρ hk₂L hu.1 hu.2 hsplit⟩

/-! ## The bounded-input large case, assembled -/

/-! ## The target -/

end

end Work.KMTAreas.A7Hi
