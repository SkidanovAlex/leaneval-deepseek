import Mathlib

namespace Work.EKLRelCross

theorem tent_iSup_ofReal_formula {a b : ℝ} (hab : a < b) (t : ℝ) :
    (⨆ n : ℕ, ENNReal.ofReal (max 0 (min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))))))
      = (Set.Ioo a b).indicator (fun _ => (1 : ENNReal)) t := by
  by_cases ht : t ∈ Set.Ioo a b
  · rw [Set.indicator_of_mem ht]
    refine le_antisymm (iSup_le fun n => ?_) ?_
    · exact ENNReal.ofReal_le_one.mpr (max_le zero_le_one (min_le_left _ _))
    · obtain ⟨N, hN⟩ := exists_nat_ge (1 / min (t - a) (b - t))
      have hδpos : (0 : ℝ) < min (t - a) (b - t) :=
        lt_min (by linarith [ht.1]) (by linarith [ht.2])
      have hNδ : (1 : ℝ) ≤ (N : ℝ) * min (t - a) (b - t) := by
        rw [div_le_iff₀ hδpos] at hN; exact hN
      have hNt : (1 : ℝ) ≤ (N : ℝ) * (t - a) := by
        have h1 : min (t - a) (b - t) ≤ t - a := min_le_left _ _
        nlinarith [hNδ, h1, (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
      have hNb : (1 : ℝ) ≤ (N : ℝ) * (b - t) := by
        have h1 : min (t - a) (b - t) ≤ b - t := min_le_right _ _
        nlinarith [hNδ, h1, (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
      have hmin : (1 : ℝ) ≤ min ((N : ℝ) * (t - a)) ((N : ℝ) * (b - t)) := le_min hNt hNb
      have hval : max 0 (min 1 (min ((N : ℝ) * (t - a)) ((N : ℝ) * (b - t)))) = 1 := by
        rw [min_eq_left hmin, max_eq_right zero_le_one]
      have hPN : ENNReal.ofReal
          (max 0 (min 1 (min ((N : ℝ) * (t - a)) ((N : ℝ) * (b - t))))) = 1 := by
        rw [hval, ENNReal.ofReal_one]
      exact le_iSup_of_le N (le_of_eq hPN.symm)
  · rw [Set.indicator_of_notMem ht]
    have ht' : t ≤ a ∨ b ≤ t := by
      by_cases h : t ≤ a
      · exact Or.inl h
      · exact Or.inr (le_of_not_gt fun hb => ht ⟨lt_of_not_ge h, hb⟩)
    have hz : ∀ n : ℕ, ENNReal.ofReal
        (max 0 (min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))))) = 0 := by
      intro n
      apply ENNReal.ofReal_eq_zero.mpr
      apply max_le le_rfl
      refine le_trans (min_le_right _ _) ?_
      rcases ht' with ht | ht
      · exact le_trans (min_le_left _ _)
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith))
      · exact le_trans (min_le_right _ _)
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith))
    apply le_antisymm
    · exact iSup_le fun n => by rw [hz n]
    · exact bot_le

end Work.EKLRelCross
