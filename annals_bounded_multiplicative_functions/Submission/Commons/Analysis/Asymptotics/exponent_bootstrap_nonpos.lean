import Mathlib
import Submission.Commons.Analysis.Asymptotics.liminf_recursion_nonpos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Asymptotics

theorem exponent_bootstrap_nonpos {k : ℕ} (hk : 2 ≤ k) (η : ℝ) (A : ℕ → ℝ → ℝ)
    (hA0 : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), A 0 b = η * (1 - b))
    (hbdd : ∀ l, l ≤ k → ∃ M : ℝ, ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |(η - A l b) / b| ≤ M)
    (hrec : ∀ l, 1 ≤ l → l ≤ k - 1 → ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      A l b ≤ (1 / ((k : ℝ) - (l : ℝ) + 1))
          * A (k - l) ((((k : ℝ) - (l : ℝ) + 1) / (l : ℝ)) * b)
        + (((k : ℝ) - (l : ℝ)) / ((k : ℝ) - (l : ℝ) + 1)) * A (l - 1) b) :
    η ≤ 0 := by
  set β : ℕ → ℝ → ℝ := fun l b => (η - A l b) / b with hβ
  have hβapply : ∀ l b, β l b = (η - A l b) / b := fun l b => by simp [hβ]
  have hbdd' : ∀ l, l ≤ k → ∃ M : ℝ, ∀ᶠ b in nhdsWithin (0:ℝ) (Set.Ioi 0),
      |β l b| ≤ M := by
    intro l hl
    obtain ⟨M, hM⟩ := hbdd l hl
    exact ⟨M, by filter_upwards [hM] with b hb; rw [hβapply]; exact hb⟩
  have hrec' : ∀ l, 1 ≤ l → l ≤ k - 1 → ∀ᶠ b in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (1 / (l : ℝ)) * β (k - l) ((((k : ℝ) - l + 1) / (l : ℝ)) * b)
        + (((k : ℝ) - l) / ((k : ℝ) - l + 1)) * β (l - 1) b ≤ β l b := by
    intro l hl1 hl2
    have hlpos : (0:ℝ) < (l:ℝ) := by
      have : (0:ℕ) < l := by omega
      exact_mod_cast this
    have hkltl : (l:ℝ) < (k:ℝ) := by
      have : l < k := by omega
      exact_mod_cast this
    have hDpos : (0:ℝ) < (k:ℝ) - (l:ℝ) + 1 := by linarith
    have hDne : ((k:ℝ) - (l:ℝ) + 1) ≠ 0 := ne_of_gt hDpos
    have hlne : (l:ℝ) ≠ 0 := ne_of_gt hlpos
    filter_upwards [hrec l hl1 hl2, self_mem_nhdsWithin] with b hb hbpos
    have hbpos' : (0:ℝ) < b := hbpos
    simp only [hβapply]
    rw [le_div_iff₀ hbpos']
    have hX : ((1 / (l : ℝ)) * ((η - A (k - l) ((((k:ℝ)-l+1)/(l:ℝ)) * b)) / ((((k:ℝ)-l+1)/(l:ℝ)) * b))
        + (((k:ℝ)-l)/((k:ℝ)-l+1)) * ((η - A (l-1) b)/b)) * b
        = η - ((1/((k:ℝ)-l+1)) * A (k-l) ((((k:ℝ)-l+1)/(l:ℝ))*b)
            + (((k:ℝ)-l)/((k:ℝ)-l+1)) * A (l-1) b) := by
      have hcne : (((k:ℝ)-l+1)/(l:ℝ)) ≠ 0 := div_ne_zero hDne hlne
      have hbne : b ≠ 0 := ne_of_gt hbpos'
      field_simp
      ring
    rw [hX]
    linarith
  have hβ0 : ∀ᶠ b in nhdsWithin (0:ℝ) (Set.Ioi 0), β 0 b = η := by
    filter_upwards [hA0, self_mem_nhdsWithin] with b hb hbpos
    have hbpos' : (0:ℝ) < b := hbpos
    have hbne : b ≠ 0 := ne_of_gt hbpos'
    simp only [hβapply]
    rw [hb]
    field_simp
    ring
  by_contra h
  have hηpos : (0:ℝ) < η := not_le.mp h
  have hcontra := liminf_recursion_nonpos hk β hbdd' hrec' η hηpos
  apply hcontra
  filter_upwards [hβ0] with b hb
  rw [hb]

end Commons.Analysis.Asymptotics
