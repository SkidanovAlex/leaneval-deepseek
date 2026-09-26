import Mathlib
import Submission.Work.CoreTopology.Disk

namespace Work.CoreTopology

theorem homDim_const {d : ℝ → ℕ} {D : ℕ} (hD : 1 < D)
    (hval : ∀ t : ℝ, d t = 0 ∨ d t = D)
    (hstep : ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ, |s - t| ≤ δ → d s ≤ d t + 1 ∧ d t ≤ d s + 1)
    (h0 : d 0 = D) : d 1 = D := by
  obtain ⟨δ, hδpos, hδ⟩ := hstep
  have hconst : ∀ s t : ℝ, |s - t| ≤ δ → d s = d t := by
    intro s t hst
    obtain ⟨h1, h2⟩ := hδ s t hst
    rcases hval s with hs | hs <;> rcases hval t with ht | ht
    · rw [hs, ht]
    · exfalso; rw [hs, ht] at h2; omega
    · exfalso; rw [hs, ht] at h1; omega
    · rw [hs, ht]
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNcast : (0 : ℝ) < N := lt_trans (by positivity : (0 : ℝ) < 1 / δ) hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNcast
  have hle : 1 / (N : ℝ) ≤ δ := by
    have hlt : (1 : ℝ) < (N : ℝ) * δ := (div_lt_iff₀ hδpos).mp hN
    rw [div_le_iff₀ hNcast]
    linarith
  have hkey : ∀ k : ℕ, d ((k : ℝ) / (N : ℝ)) = D := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hpdiff : |(k : ℝ) / (N : ℝ) - (((k + 1 : ℕ)) : ℝ) / (N : ℝ)| ≤ δ := by
        rw [hcast]
        have hsub : (k : ℝ) / (N : ℝ) - ((k : ℝ) + 1) / (N : ℝ) = -(1 / (N : ℝ)) := by
          field_simp
          ring
        rw [hsub, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
        exact hle
      have hstep2 := hconst ((k : ℝ) / (N : ℝ)) ((((k + 1 : ℕ)) : ℝ) / (N : ℝ)) hpdiff
      rw [← hstep2, ih]
  have hfin := hkey N
  rw [div_self hNne] at hfin
  exact hfin

end Work.CoreTopology
