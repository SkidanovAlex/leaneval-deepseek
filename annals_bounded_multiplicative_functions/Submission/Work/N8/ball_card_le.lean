import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- A finite set of reals, all in the ball `|x - A| ≤ r` and pairwise `B`-separated,
has cardinality at most `2r/B + 1`.

The proof sorts the points increasingly (via `Finset.orderEmbOfFin`) and telescopes
the consecutive gaps: the `card - 1` gaps are each at least `B`, so
`(card - 1) * B ≤ max - min ≤ 2r`. -/
theorem ball_card_le (r B A : ℝ) (hr : 0 < r) (hB : 0 < B) (s : Finset ℝ)
    (h1 : ∀ x ∈ s, |x - A| ≤ r) (h2 : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → B ≤ |x - y|) :
    ((s.card : ℕ) : ℝ) ≤ 2 * r / B + 1 := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [h0]
    push_cast
    have : (0 : ℝ) < 2 * r / B := div_pos (by linarith) hB
    linarith
  · -- `f` enumerates `s` in increasing order.
    let f : Fin s.card ↪o ℝ := s.orderEmbOfFin rfl
    have hmem : ∀ i : Fin s.card, f i ∈ s := by
      intro i
      exact Finset.orderEmbOfFin_mem s rfl i
    -- total version of `f` on `ℕ`, so that `Finset.sum_range_sub` applies
    let g : ℕ → ℝ := fun i => if h : i < s.card then (f ⟨i, h⟩ : ℝ) else 0
    have hgi : ∀ (i : ℕ) (h : i < s.card), g i = f ⟨i, h⟩ := by
      intro i h
      simp only [g, dite_eq_left h]
    -- each consecutive gap is at least `B`
    have hterm : ∀ i ∈ Finset.range (s.card - 1), B ≤ g (i + 1) - g i := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hi1 : i < s.card := by omega
      have hi2 : i + 1 < s.card := by omega
      rw [hgi i hi1, hgi (i + 1) hi2]
      have hlt : (⟨i, hi1⟩ : Fin s.card) < ⟨i + 1, hi2⟩ := by
        rw [Fin.lt_def]; simp
      have hlt' : f ⟨i, hi1⟩ < f ⟨i + 1, hi2⟩ := f.lt_iff_lt.mpr hlt
      have hfin : (⟨i + 1, hi2⟩ : Fin s.card) ≠ ⟨i, hi1⟩ := by
        intro h; rw [Fin.mk.injEq] at h; omega
      have hne : f ⟨i + 1, hi2⟩ ≠ f ⟨i, hi1⟩ := fun hcon => hfin (f.injective hcon)
      have h2' := h2 (f ⟨i + 1, hi2⟩) (hmem _) (f ⟨i, hi1⟩) (hmem _) hne
      rw [abs_of_pos (sub_pos.mpr hlt')] at h2'
      exact h2'
    have hsum_ge : ((s.card - 1 : ℕ) : ℝ) * B
        ≤ ∑ i ∈ Finset.range (s.card - 1), (g (i + 1) - g i) := by
      have hconst : ∑ i ∈ Finset.range (s.card - 1), B = ((s.card - 1 : ℕ) : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← hconst]
      exact Finset.sum_le_sum hterm
    -- the telescoping sum is `max - min`
    have htel := Finset.sum_range_sub g (s.card - 1)
    rw [htel] at hsum_ge
    have hglast : g (s.card - 1) = f ⟨s.card - 1, by omega⟩ := hgi _ (by omega)
    have hg0 : g 0 = f ⟨0, hpos⟩ := hgi _ hpos
    rw [hglast, hg0] at hsum_ge
    have hupper : f ⟨s.card - 1, by omega⟩ - f ⟨0, hpos⟩ ≤ 2 * r := by
      have ha := h1 _ (hmem ⟨s.card - 1, by omega⟩)
      have hb := h1 _ (hmem ⟨0, hpos⟩)
      rw [abs_le] at ha hb
      linarith [ha.1, ha.2, hb.1, hb.2]
    have hmain : ((s.card - 1 : ℕ) : ℝ) * B ≤ 2 * r := le_trans hsum_ge hupper
    have hcast : ((s.card - 1 : ℕ) : ℝ) = (s.card : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ s.card)]
      norm_num
    rw [hcast] at hmain
    have hfinal : (s.card : ℝ) - 1 ≤ 2 * r / B := by
      rw [le_div_iff₀ hB]
      linarith
    linarith

end Work.N8
