import Mathlib

namespace Work.Pert.V5

theorem ceil_cover_norm_le {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a c m P : ℝ}
    (hac : a ≤ c) (hm : 0 < m) (hP : 0 ≤ P)
    (h : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ c → y - x ≤ m → ‖f y - f x‖ ≤ P) :
    ‖f c - f a‖ ≤ (Nat.ceil ((c - a) / m) : ℝ) * P := by
  have key : ∀ n : ℕ, 0 < n → c - a ≤ (n : ℝ) * m →
      ‖f c - f a‖ ≤ (n : ℝ) * P := by
    intro n hn_pos hnm
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    set d : ℝ := (c - a) / n with hd
    set g : ℕ → ℝ := fun i => a + (i : ℝ) * d with hgdef
    have hd_nonneg : 0 ≤ d := by
      rw [hd]; exact div_nonneg (by linarith) (le_of_lt hnR)
    have hdm : d ≤ m := by
      rw [hd, div_le_iff₀ hnR]
      calc c - a ≤ (n : ℝ) * m := hnm
        _ = m * (n : ℝ) := by ring
    have hg0 : g 0 = a := by simp [g]
    have hgn : g n = c := by
      simp only [g]
      rw [hd, mul_div_cancel₀ _ hnne]
      ring
    have hgmono : ∀ i j : ℕ, i ≤ j → g i ≤ g j := by
      intro i j hij
      simp only [g]
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      have : (i : ℝ) * d ≤ (j : ℝ) * d := mul_le_mul_of_nonneg_right hij' hd_nonneg
      linarith
    have hgdiff : ∀ i : ℕ, g (i + 1) - g i = d := by
      intro i
      simp only [g]
      push_cast
      ring
    have hstep : ∀ i ∈ Finset.range n, ‖f (g (i + 1)) - f (g i)‖ ≤ P := by
      intro i hi
      simp only [Finset.mem_range] at hi
      refine h (g i) (g (i + 1)) ?_ ?_ ?_ ?_
      · simp only [g]
        have : (0 : ℝ) ≤ (i : ℝ) * d := mul_nonneg (by positivity) hd_nonneg
        linarith
      · exact hgmono i (i + 1) (Nat.le_succ i)
      · rw [← hgn]; exact hgmono (i + 1) n (Nat.succ_le_of_lt hi)
      · rw [hgdiff i]; exact hdm
    have hsum : ∑ i ∈ Finset.range n, (f (g (i + 1)) - f (g i)) = f c - f a := by
      rw [Finset.sum_range_sub (f := fun i => f (g i))]
      rw [hgn, hg0]
    calc ‖f c - f a‖ = ‖∑ i ∈ Finset.range n, (f (g (i + 1)) - f (g i))‖ := by
            rw [hsum]
      _ ≤ ∑ i ∈ Finset.range n, ‖f (g (i + 1)) - f (g i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, P := Finset.sum_le_sum hstep
      _ = (n : ℝ) * P := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rcases eq_or_lt_of_le hac with hca | hclt
  · subst hca; simp
  · refine key (Nat.ceil ((c - a) / m)) ?_ ?_
    · rw [Nat.ceil_pos]; exact div_pos (by linarith) hm
    · have h1 : (c - a) / m ≤ (Nat.ceil ((c - a) / m) : ℝ) := Nat.le_ceil _
      rw [div_le_iff₀ hm] at h1
      exact h1

end Work.Pert.V5
