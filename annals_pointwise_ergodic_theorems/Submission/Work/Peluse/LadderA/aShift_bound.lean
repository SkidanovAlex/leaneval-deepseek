import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

open scoped BigOperators

/-- **The shift bound of the ladder.**

If every coefficient `p i a` satisfies the paper's non-degeneracy hypothesis
`|p i a| · M₁ · M₂ ≤ D · N` and every entry of `a''` on the window `ω` is bounded by `M₂`, then
`|∑_{s ∈ ω} p s.1 a · a'' s|` is at most `(#(Slot ι k) · D + 3) · Nw / M₁`.

The point is that *each* slot contributes at most `D·N / M₁`: on the one hand `|a'' s| ≤ M₂`, on
the other `|p s.1 a| · M₂ ≤ (D·N)/M₁` by the shift hypothesis (`M₁ > 0`), and the number of terms is
at most `#(Slot ι k)`.  Finally `#ω · (D·N/M₁) ≤ (#Slot·D)·N/M₁ ≤ ((#Slot·D)+3)·Nw/M₁` because
`N ≤ Nw`, the `+3` slack absorbing the rounding. -/
theorem aShift_bound {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (p : ι → (Fin n → ℤ) → ℤ)
    {M₁ M₂ N Nw D : ℕ} {a : Fin n → ℤ} (a'' : Work.Peluse.UControl.Slot ι k → ℤ)
    (ω : Finset (Work.Peluse.UControl.Slot ι k))
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hNM : M₁ ≤ N) (hNN : N ≤ Nw)
    (hbox : ∀ s ∈ ω, |a'' s| < (M₂ : ℤ))
    (hp : ∀ i : ι, |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) :
    |∑ s ∈ ω, p s.1 a * a'' s| ≤
      ((Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) / (M₁ : ℤ) := by
  classical
  have hM1pos : (0 : ℤ) < (M₁ : ℤ) := by
    have : (1 : ℤ) ≤ (M₁ : ℤ) := by exact_mod_cast hM₁
    linarith
  -- Each slot contributes at most `D·N/M₁`.
  have hstep : ∀ s ∈ ω, |p s.1 a * a'' s| ≤ (D : ℤ) * (N : ℤ) / (M₁ : ℤ) := by
    intro s hs
    rw [abs_mul]
    have hM₂le : |a'' s| ≤ (M₂ : ℤ) := le_of_lt (hbox s hs)
    have hpz : |p s.1 a| * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ) / (M₁ : ℤ) := by
      rw [Int.le_ediv_iff_mul_le hM1pos]
      calc (|p s.1 a| * (M₂ : ℤ)) * (M₁ : ℤ)
          = |p s.1 a| * (M₁ : ℤ) * (M₂ : ℤ) := by ring
        _ ≤ (D : ℤ) * (N : ℤ) := hp s.1
    calc |p s.1 a| * |a'' s| ≤ |p s.1 a| * (M₂ : ℤ) :=
          mul_le_mul_of_nonneg_left hM₂le (abs_nonneg _)
      _ ≤ (D : ℤ) * (N : ℤ) / (M₁ : ℤ) := hpz
  have hq_nn : (0 : ℤ) ≤ (D : ℤ) * (N : ℤ) / (M₁ : ℤ) :=
    Int.ediv_nonneg (by positivity) (le_of_lt hM1pos)
  -- Sum over the window.
  have hsum : |∑ s ∈ ω, p s.1 a * a'' s|
      ≤ (ω.card : ℤ) * ((D : ℤ) * (N : ℤ) / (M₁ : ℤ)) := by
    calc |∑ s ∈ ω, p s.1 a * a'' s|
        ≤ ∑ s ∈ ω, |p s.1 a * a'' s| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ ω, (D : ℤ) * (N : ℤ) / (M₁ : ℤ) := Finset.sum_le_sum hstep
      _ = (ω.card : ℤ) * ((D : ℤ) * (N : ℤ) / (M₁ : ℤ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : (ω.card : ℤ) ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) := by
    exact_mod_cast Finset.card_le_univ ω
  -- The final arithmetic: `#ω · (D·N/M₁) ≤ ((#Slot)·D+3)·Nw/M₁`.
  have hfin : (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) *
        ((D : ℤ) * (N : ℤ) / (M₁ : ℤ))
      ≤ ((Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) / (M₁ : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hM1pos]
    have h1 : ((D : ℤ) * (N : ℤ) / (M₁ : ℤ)) * (M₁ : ℤ) ≤ (D : ℤ) * (N : ℤ) :=
      Int.ediv_mul_le _ (ne_of_gt hM1pos)
    have h2 : (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) *
          (((D : ℤ) * (N : ℤ) / (M₁ : ℤ)) * (M₁ : ℤ))
        ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * ((D : ℤ) * (N : ℤ)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * ((D : ℤ) * (N : ℤ))
        ≤ ((Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) := by
      have hNwN : (N : ℤ) ≤ (Nw : ℤ) := by exact_mod_cast hNN
      have hCD : (0 : ℤ) ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * (D : ℤ) := by
        positivity
      push_cast
      have h4 : (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * (D : ℤ) * (N : ℤ)
          ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * (D : ℤ) * (Nw : ℤ) :=
        mul_le_mul_of_nonneg_left hNwN hCD
      have h5 : (0 : ℤ) ≤ 3 * (Nw : ℤ) := by positivity
      linarith
    calc (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) *
            ((D : ℤ) * (N : ℤ) / (M₁ : ℤ)) * (M₁ : ℤ)
        = (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) *
            (((D : ℤ) * (N : ℤ) / (M₁ : ℤ)) * (M₁ : ℤ)) := by ring
      _ ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * ((D : ℤ) * (N : ℤ)) := h2
      _ ≤ ((Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) := h3
  calc |∑ s ∈ ω, p s.1 a * a'' s|
      ≤ (ω.card : ℤ) * ((D : ℤ) * (N : ℤ) / (M₁ : ℤ)) := hsum
    _ ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) *
          ((D : ℤ) * (N : ℤ) / (M₁ : ℤ)) := mul_le_mul_of_nonneg_right hcard hq_nn
    _ ≤ ((Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) / (M₁ : ℤ) :=
          hfin

end Work.Peluse.LadderA
