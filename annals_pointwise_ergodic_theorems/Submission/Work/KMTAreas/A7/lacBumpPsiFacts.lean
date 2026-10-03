import Mathlib
import Submission.Work.KMTAreas.A7.lacBumpDefs

namespace Work.KMTAreas.A7

theorem lacBumpPsiFacts :
    Work.KMTAreas.A7.lacψ 0 = 0 ∧
    (∀ ξ : ℝ, 1 < |ξ| → Work.KMTAreas.A7.lacψ ξ = 0) ∧
    (∀ ξ : ℝ, ‖Work.KMTAreas.A7.lacψ ξ‖ ≤ 8 * min 1 |ξ|) ∧
    (∀ N k₁ : ℕ, 0 < Work.KMTAreas.A7.lacσ N k₁) ∧
    (∀ N k₁ : ℕ, 1 ≤ N → (N : ℝ) / Work.KMTAreas.A7.lacσ N k₁ ≤ (2 : ℝ) ^ (k₁ + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [lacψ]
  · intro ξ hξ
    have h1 : Work.KMTContract.kmtEta ξ = 0 := Work.KMTContract.kmtEta_zero (le_of_lt hξ)
    have h2 : Work.KMTContract.kmtEta (2 * ξ) = 0 := by
      apply Work.KMTContract.kmtEta_zero
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    simp [lacψ, h1, h2]
  · intro ξ
    have hle : ‖lacψ ξ‖ ≤ 2 := by
      rw [lacψ]
      calc ‖Work.KMTContract.kmtEta ξ - Work.KMTContract.kmtEta (2 * ξ)‖
          ≤ ‖Work.KMTContract.kmtEta ξ‖ + ‖Work.KMTContract.kmtEta (2 * ξ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 :=
            add_le_add (Work.KMTContract.norm_kmtEta_le _) (Work.KMTContract.norm_kmtEta_le _)
        _ = 2 := by norm_num
    rcases le_or_gt |ξ| (1 / 4 : ℝ) with h | h
    · have h1 : Work.KMTContract.kmtEta ξ = 1 :=
        Work.KMTContract.kmtEta_one (by linarith)
      have h2 : Work.KMTContract.kmtEta (2 * ξ) = 1 := by
        apply Work.KMTContract.kmtEta_one
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      have hz : lacψ ξ = 0 := by simp [lacψ, h1, h2]
      rw [hz, norm_zero]
      exact mul_nonneg (by norm_num) (le_min zero_le_one (abs_nonneg ξ))
    · have hmin : (1 / 4 : ℝ) < min 1 |ξ| := lt_min (by norm_num) h
      have : (2 : ℝ) < 8 * min 1 |ξ| := by linarith
      linarith [hle]
  · intro N k₁
    simp only [lacσ]
    exact zpow_pos (by norm_num : (0 : ℝ) < 2) _
  · intro N k₁ hN
    have hNle : (N : ℝ) ≤ (2 : ℝ) ^ (Work.Analysis.EndVar.logN N + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
      have h' : ((max N 2 : ℕ) : ℝ) < ((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℕ) := by
        exact_mod_cast h
      push_cast at h'
      have hcast : ((Nat.log 2 (max N 2) + 1 : ℕ) : ℤ) = Work.Analysis.EndVar.logN N + 1 := by
        simp only [Work.Analysis.EndVar.logN]
        push_cast
        ring
      rw [← zpow_natCast (2 : ℝ) (Nat.log 2 (max N 2) + 1), hcast] at h'
      exact (lt_of_le_of_lt (by exact_mod_cast le_max_left N 2) h').le
    have hpos : (0 : ℝ) < lacσ N k₁ := by
      simp only [lacσ]; exact zpow_pos (by norm_num : (0 : ℝ) < 2) _
    rw [div_le_iff₀ hpos]
    refine hNle.trans_eq ?_
    simp only [lacσ]
    rw [show (2 : ℝ) ^ (k₁ + 1) = (2 : ℝ) ^ (((k₁ + 1 : ℕ) : ℤ)) from
      (zpow_natCast 2 (k₁ + 1)).symm]
    rw [show (((k₁ + 1 : ℕ) : ℤ)) = (k₁ : ℤ) + 1 by push_cast; ring]
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring

end Work.KMTAreas.A7
