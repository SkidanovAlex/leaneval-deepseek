/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IonescuWainger.MajorArcs

/-!
# Nesting of the Littlewood–Paley cutoffs

The paper's cutoffs are `η_{≤k}(θ) = η(θ/2^k)` for a fixed smooth even `η` which equals `1` on
`[-1/2, 1/2]` and vanishes off `[-1, 1]`.  For `k' < k` one has `η_{≤k} · η_{≤k'} = η_{≤k'}`, which
is the identity behind the martingale-like nesting of the Ionescu–Wainger projections
`Π_{≤l,≤k} ∘ Π_{≤l',≤k'}`.
-/

set_option autoImplicit false

namespace Work.Analysis.IonescuWainger

/-- Littlewood–Paley nesting: for `k' < k`, `η_{≤k} · η_{≤k'} = η_{≤k'}`. -/
theorem etaCut_mul {η : ℝ → ℂ} (hη1 : ∀ x, |x| ≤ 1 / 2 → η x = 1)
    (hη0 : ∀ x, 1 < |x| → η x = 0) {k k' : ℤ} (hk : k' < k) :
    etaCut η k * etaCut η k' = etaCut η k' := by
  funext θ
  simp only [Pi.mul_apply, etaCut]
  by_cases h : η (θ / (2 : ℝ) ^ k') = 0
  · rw [h, mul_zero]
  · have hk'pos : (0 : ℝ) < (2 : ℝ) ^ k' := zpow_pos (by norm_num) _
    have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    have hle : |θ / (2 : ℝ) ^ k'| ≤ 1 := by
      by_contra hc
      exact h (hη0 _ (not_le.mp hc))
    have hθ : |θ| ≤ (2 : ℝ) ^ k' := by
      have h1 : (2 : ℝ) ^ k' * |θ / (2 : ℝ) ^ k'| = |θ| := by
        rw [abs_div, abs_of_pos hk'pos, mul_div_cancel₀ _ hk'pos.ne']
      rw [← h1]
      exact mul_le_of_le_one_right hk'pos.le hle
    have h2 : |θ / (2 : ℝ) ^ k| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hkpos, div_le_iff₀ hkpos]
      have hmono : (2 : ℝ) ^ k' ≤ (2 : ℝ) ^ (k - 1) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      have hsplit : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
        rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      calc |θ| ≤ (2 : ℝ) ^ k' := hθ
        _ ≤ (2 : ℝ) ^ (k - 1) := hmono
        _ = (2 : ℝ) ^ k / 2 := hsplit
        _ = (1 / 2) * (2 : ℝ) ^ k := by ring
    rw [hη1 _ h2, one_mul]

end Work.Analysis.IonescuWainger
