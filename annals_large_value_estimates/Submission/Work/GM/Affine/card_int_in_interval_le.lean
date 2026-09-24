import Mathlib

namespace Work.GM.Affine

/-- **Counting integers in a short interval.** If every `n` in a `Finset ℤ` satisfies
`|n - ξ| ≤ r` with `r ≥ 0`, then the finset has at most `2r + 1` elements (`r` real). -/
lemma card_int_in_interval_le {r ξ : ℝ} (hr : 0 ≤ r) (Q : Finset ℤ)
    (hQ : ∀ n ∈ Q, |(n : ℝ) - ξ| ≤ r) : (Q.card : ℝ) ≤ 2 * r + 1 := by
  rcases Q.eq_empty_or_nonempty with h | hne
  · rw [h, Finset.card_empty]; norm_num; linarith
  · -- `Q` lies in `[min' Q, max' Q]`, an interval of at most `2r + 1` integers.
    have hAq : Q.min' hne ∈ Q := Q.min'_mem hne
    have hBq : Q.max' hne ∈ Q := Q.max'_mem hne
    have hsub : Q ⊆ Finset.Icc (Q.min' hne) (Q.max' hne) := fun n hn =>
      Finset.mem_Icc.mpr ⟨Q.min'_le n hn, Q.le_max' n hn⟩
    have hcard := Finset.card_le_card hsub
    rw [Int.card_Icc] at hcard
    -- length of the interval is at most `2r`
    have hBA : (Q.max' hne : ℝ) - (Q.min' hne : ℝ) ≤ 2 * r := by
      have h1 := (abs_le.mp (hQ _ hAq)).1
      have h2 := (abs_le.mp (hQ _ hBq)).2
      linarith
    have hAB : Q.min' hne ≤ Q.max' hne := Q.min'_le _ hBq
    have hpos : (0 : ℤ) ≤ Q.max' hne + 1 - Q.min' hne := by omega
    have hcast : ((Q.max' hne + 1 - Q.min' hne).toNat : ℝ)
        = (Q.max' hne : ℝ) + 1 - (Q.min' hne : ℝ) := by
      have h1 : ((Q.max' hne + 1 - Q.min' hne).toNat : ℝ)
          = (((Q.max' hne + 1 - Q.min' hne).toNat : ℤ) : ℝ) := by push_cast; ring
      rw [h1, Int.toNat_of_nonneg hpos]; push_cast; ring
    have hle : ((Q.max' hne + 1 - Q.min' hne).toNat : ℝ) ≤ 2 * r + 1 := by
      rw [hcast]; linarith
    exact le_trans (Nat.cast_le.mpr hcard) hle

end Work.GM.Affine
