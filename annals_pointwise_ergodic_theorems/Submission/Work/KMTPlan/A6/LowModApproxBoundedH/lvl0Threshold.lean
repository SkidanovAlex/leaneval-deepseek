import Mathlib
import Submission.Work.KMTAreas.A7.goodRegime
import Submission.Work.KMTAreas.A7.ExceptionalSupport

namespace Work.KMTPlan.A6.LowModApproxBoundedH

/-- Auxiliary: `n ≤ 2 ^ n`. -/
private theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      calc m + 1 ≤ 2 ^ m + 1 := by omega
        _ ≤ 2 ^ m + 2 ^ m := by
            have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
            omega
        _ = 2 ^ (m + 1) := by ring

theorem lvl0Threshold (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (B : ℕ) :
    ∃ T : ℕ, ∀ (l₁ l₂ k₁ k₂ : ℕ), Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → ∀ N : ℕ, T ≤ N →
      Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N ∧
        Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N ∧
          Work.KMTAreas.A7.mainRegime ρ k₁ k₂ N := by
  refine ⟨max (max (2 ^ (2 ^ B)) (Work.KMTAreas.A7.splitCut ρ B + 1))
      (2 ^ (B + 2 * Work.KMTAreas.A7.uScale ρ B + 1)), ?_⟩
  intro l₁ l₂ k₁ k₂ hlL N hN
  have hl₁ : l₁ ≤ B := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hlL
  have hl₂ : l₂ ≤ B := le_trans (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) hlL
  have hk₁ : k₁ ≤ B := le_trans (le_trans (le_max_left k₁ k₂) (le_max_right _ _)) hlL
  have hk₂ : k₂ ≤ B := le_trans (le_trans (le_max_right k₁ k₂) (le_max_right _ _)) hlL
  have hmaxk : max k₁ k₂ ≤ B := le_trans (le_max_right _ _) hlL
  have hT₁ : 2 ^ (2 ^ B) ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hT₂ : Work.KMTAreas.A7.splitCut ρ B + 1 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hT₃ : 2 ^ (B + 2 * Work.KMTAreas.A7.uScale ρ B + 1) ≤ N :=
    le_trans (le_max_right _ _) hN
  have hN2 : 2 ≤ N := by
    have : 2 ≤ 2 ^ (2 ^ B) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (2 ^ B) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)
    omega
  have hheight : B ≤ Work.Analysis.EndVar.heightScale C₀ N := by
    have h2B : 2 ^ B ≤ Nat.log 2 (max N 2) := by
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      calc 2 ^ (2 ^ B) ≤ N := hT₁
        _ ≤ max N 2 := le_max_left _ _
    have hB : B ≤ Nat.log 2 (Nat.log 2 (max N 2) + 2) := by
      have h1 : B ≤ Nat.log 2 (2 ^ B) := le_of_eq (Nat.log_pow (by norm_num : 1 < 2) B).symm
      refine h1.trans (Nat.log_mono_right ?_)
      omega
    rw [Work.Analysis.EndVar.heightScale, Work.Analysis.EndVar.logLogN]
    calc B = 1 * B := (one_mul B).symm
      _ ≤ C₀ * Nat.log 2 (Nat.log 2 (max N 2) + 2) := Nat.mul_le_mul hC₀ hB
  refine ⟨?_, ?_, ?_⟩
  · rw [Work.Analysis.EndVar.inIndexSet_iff_le]
    exact ⟨le_trans hl₁ hheight, le_trans hl₂ hheight,
      le_trans hk₁ hheight, le_trans hk₂ hheight⟩
  · have hmono : Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
        ≤ Work.KMTAreas.A7.splitCut ρ B := by
      have h1 : Work.Analysis.EndVar.scaleCount 1 ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
          ≤ Work.Analysis.EndVar.scaleCount 1 ρ B :=
        Work.KMTAreas.A7.ExcSupport.scaleCount_mono 1 hρ.le hlL
      exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h1)
    have heq : Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
        = Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) := rfl
    rw [heq]
    exact lt_of_le_of_lt hmono (Nat.lt_of_succ_le hT₂)
  · have hlogN : B + 2 * Work.KMTAreas.A7.uScale ρ B
        ≤ (Work.Analysis.EndVar.logN N).toNat := by
      have h1 : B + 2 * Work.KMTAreas.A7.uScale ρ B ≤ Nat.log 2 (max N 2) := by
        refine Nat.le_log_of_pow_le (by norm_num) ?_
        calc 2 ^ (B + 2 * Work.KMTAreas.A7.uScale ρ B)
            ≤ 2 ^ (B + 2 * Work.KMTAreas.A7.uScale ρ B + 1) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ N := hT₃
          _ ≤ max N 2 := le_max_left _ _
      rw [Work.Analysis.EndVar.logN, Int.toNat_natCast]
      exact h1
    have hus : Work.KMTAreas.A7.uScale ρ (max k₁ k₂) ≤ Work.KMTAreas.A7.uScale ρ B :=
      Work.KMTAreas.A7.uScale_mono hρ.le hmaxk
    refine ⟨?_, ?_⟩ <;> omega

end Work.KMTPlan.A6.LowModApproxBoundedH
