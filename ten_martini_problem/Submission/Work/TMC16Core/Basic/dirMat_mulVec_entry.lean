import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

/-- The diagonal contribution to `dirMat · w`: only the `i`-th term survives. -/
private lemma sumDiag {n : ℕ} (w : Fin n → ℂ) (i : Fin n) (D : ℂ) :
    (∑ j : Fin n, (if i = j then D else 0) * w j) = D * w i := by
  rw [Finset.sum_eq_single (s := Finset.univ)
      (f := fun j : Fin n => (if i = j then D else 0) * w j) i]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm), zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- The upper off-diagonal contribution to `dirMat · w`: the term `w ⟨i+1, _⟩` when `i+1 < n`. -/
private lemma sumUpper {n : ℕ} (w : Fin n → ℂ) (i : Fin n) :
    (∑ j : Fin n, (if ((i:ℕ):ℤ) + 1 = ((j:ℕ):ℤ) then (1:ℂ) else 0) * w j)
      = (if h : (i:ℕ)+1 < n then w ⟨(i:ℕ)+1, h⟩ else 0) := by
  by_cases h : (i:ℕ)+1 < n
  · rw [dif_pos h]
    have key := Finset.sum_eq_single (s := Finset.univ)
        (f := fun j : Fin n => (if ((i:ℕ):ℤ) + 1 = ((j:ℕ):ℤ) then (1:ℂ) else 0) * w j)
        (⟨(i:ℕ)+1, h⟩ : Fin n)
        (by
          intro b _ hb
          have hc : ¬ (((i:ℕ):ℤ) + 1 = ((b:ℕ):ℤ)) := by
            intro hc
            apply hb
            apply Fin.ext
            have this : ((b:ℕ):ℤ) = (((i:ℕ)+1 : ℕ) : ℤ) := by rw [← hc]; push_cast; ring
            exact Int.ofNat_inj.mp this
          rw [if_neg hc, zero_mul])
        (by intro hmem; exact absurd (Finset.mem_univ _) hmem)
    rw [key, if_pos (by push_cast; ring), one_mul]
  · rw [dif_neg h]
    refine Finset.sum_eq_zero ?_
    intro b _
    have hc : ¬ (((i:ℕ):ℤ) + 1 = ((b:ℕ):ℤ)) := by
      intro hc
      have : (b:ℕ) = (i:ℕ) + 1 := by
        have : ((b:ℕ):ℤ) = ((i:ℕ):ℤ) + 1 := hc.symm
        exact Int.ofNat_inj.mp this
      omega
    rw [if_neg hc, zero_mul]

/-- The lower off-diagonal contribution to `dirMat · w`: the term `w ⟨i-1, _⟩` when `0 < i`. -/
private lemma sumLower {n : ℕ} (w : Fin n → ℂ) (i : Fin n) :
    (∑ j : Fin n, (if ((j:ℕ):ℤ) + 1 = ((i:ℕ):ℤ) then (1:ℂ) else 0) * w j)
      = (if h : 0 < (i:ℕ) then w ⟨(i:ℕ)-1, by omega⟩ else 0) := by
  by_cases h : 0 < (i:ℕ)
  · rw [dif_pos h]
    have key := Finset.sum_eq_single (s := Finset.univ)
        (f := fun j : Fin n => (if ((j:ℕ):ℤ) + 1 = ((i:ℕ):ℤ) then (1:ℂ) else 0) * w j)
        (⟨(i:ℕ)-1, by omega⟩ : Fin n)
        (by
          intro b _ hb
          have hc : ¬ (((b:ℕ):ℤ) + 1 = ((i:ℕ):ℤ)) := by
            intro hc
            apply hb
            apply Fin.ext
            have hb' : (b:ℕ) + 1 = (i:ℕ) := by
              have : (((b:ℕ)+1 : ℕ) : ℤ) = ((i:ℕ):ℤ) := by push_cast; exact hc
              exact Int.ofNat_inj.mp this
            exact Nat.eq_sub_of_add_eq hb'
          rw [if_neg hc, zero_mul])
        (by intro hmem; exact absurd (Finset.mem_univ _) hmem)
    rw [key, if_pos (by push_cast; omega), one_mul]
  · rw [dif_neg h]
    refine Finset.sum_eq_zero ?_
    intro b _
    have hc : ¬ (((b:ℕ):ℤ) + 1 = ((i:ℕ):ℤ)) := by
      intro hc
      have : ((b:ℕ):ℤ) + 1 = ((i:ℕ):ℤ) := hc
      omega
    rw [if_neg hc, zero_mul]

theorem dirMat_mulVec_entry {α lam : ℝ} {φ : ℝ} {E : ℂ} {n : ℕ} (w : Fin n → ℂ) (i : Fin n) :
    ((Work.TMC16Core.dirMat α lam φ E n).mulVec w) i =
      (((Work.TMC16Core.amoPot α lam φ ((i:ℕ):ℤ) : ℝ) : ℂ) - E) * w i
        + (if h : (i:ℕ) + 1 < n then w ⟨(i:ℕ)+1, h⟩ else 0)
        + (if h : 0 < (i:ℕ) then w ⟨(i:ℕ)-1, by omega⟩ else 0) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Work.TMC16Core.dirMat, add_mul, Finset.sum_add_distrib]
  rw [sumDiag, sumUpper, sumLower]

end Work.TMC16Core.Basic
