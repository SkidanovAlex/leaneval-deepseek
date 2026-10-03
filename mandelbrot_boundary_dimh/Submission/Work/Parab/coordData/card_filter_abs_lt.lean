import Mathlib

namespace Work.Parab.coordData

/-- Counting bound: among the `k` first natural numbers, at most `2r + 1` satisfy
`|x + j| < r`.  Indeed the integers `j` occurring lie between the smallest and the
largest element of the (nonempty) set, and the corresponding reals `x + j` all lie
in the open interval `(-r, r)` of length `2r`. -/
theorem card_filter_abs_lt (x r : ℝ) (hr : 0 < r) (k : ℕ) :
    (((Finset.range k).filter (fun j : ℕ => |x + (j : ℝ)| < r)).card : ℝ) ≤ 2 * r + 1 := by
  set S : Finset ℕ := (Finset.range k).filter (fun j : ℕ => |x + (j : ℝ)| < r) with hS
  rcases S.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]
    simp
    linarith
  · have hmem : ∀ j ∈ S, |x + (j : ℝ)| < r := by
      intro j hj
      rw [hS] at hj
      exact (Finset.mem_filter.mp hj).2
    have hsub : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S j hj, Finset.le_max' S j hj⟩
    have hcard : S.card ≤ S.max' hne + 1 - S.min' hne := by
      have h := Finset.card_le_card hsub
      rwa [Nat.card_Icc] at h
    have hamin : |x + (S.min' hne : ℝ)| < r := hmem _ (Finset.min'_mem S hne)
    have hbmax : |x + (S.max' hne : ℝ)| < r := hmem _ (Finset.max'_mem S hne)
    have hgt : -r < x + (S.min' hne : ℝ) := (abs_lt.mp hamin).1
    have hlt : x + (S.max' hne : ℝ) < r := (abs_lt.mp hbmax).2
    have hle : S.min' hne ≤ S.max' hne + 1 := by
      have : S.min' hne ≤ S.max' hne := Finset.min'_le S _ (Finset.max'_mem S hne)
      omega
    have hcast : ((S.max' hne + 1 - S.min' hne : ℕ) : ℝ)
        = (S.max' hne : ℝ) - (S.min' hne : ℝ) + 1 := by
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
      ring
    have : (S.card : ℝ) ≤ (S.max' hne : ℝ) - (S.min' hne : ℝ) + 1 := by
      calc (S.card : ℝ) ≤ ((S.max' hne + 1 - S.min' hne : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (S.max' hne : ℝ) - (S.min' hne : ℝ) + 1 := hcast
    linarith

end Work.Parab.coordData
