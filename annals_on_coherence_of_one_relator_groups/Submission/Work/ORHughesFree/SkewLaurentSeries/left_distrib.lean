import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

open Finset

namespace Work.ORHughesFree.SkewLaurentSeries

/-- Two `Icc` sums of the same summand `w`, whose upper bounds are `n - N₁` and `n - N₂`,
agree as soon as `w` vanishes below *both* candidate lower bounds `N₁`, `N₂`, i.e. whenever
`n - k < Nᵢ`.  This is the tool that lets us replace the arbitrary `Classical.choose` lower
bound `lo` by any other valid lower bound. -/
theorem sum_Icc_congr_of_vanishing {B : Type*} [AddCommMonoid B] (w : ℤ → B)
    (Nf n N₁ N₂ : ℤ) (h₁ : ∀ k : ℤ, n - k < N₁ → w k = 0)
    (h₂ : ∀ k : ℤ, n - k < N₂ → w k = 0) :
    (∑ k ∈ Finset.Icc Nf (n - N₁), w k) = ∑ k ∈ Finset.Icc Nf (n - N₂), w k := by
  rcases le_total N₁ N₂ with hle | hle
  · symm
    apply Finset.sum_subset (s₁ := Finset.Icc Nf (n - N₂)) (s₂ := Finset.Icc Nf (n - N₁))
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      exact ⟨hx.1, by omega⟩
    · intro x hx hxs
      simp only [Finset.mem_Icc] at hx hxs
      exact h₂ x (by omega)
  · apply Finset.sum_subset (s₁ := Finset.Icc Nf (n - N₁)) (s₂ := Finset.Icc Nf (n - N₂))
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      exact ⟨hx.1, by omega⟩
    · intro x hx hxs
      simp only [Finset.mem_Icc] at hx hxs
      exact h₁ x (by omega)

theorem left_distrib {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f g h : SkewLaurentSeries A) : f * (g + h) = f * g + f * h := by
  apply Subtype.ext
  funext n
  simp only [mul_apply, add_apply]
  -- Replace the arbitrary chosen bound `(g + h).lo` by the explicit valid bound
  -- `min g.lo h.lo` for `g + h`.
  have e1 : (∑ x ∈ Icc f.lo (n - (g + h).lo),
        f.1 x * (Multiplicative.ofAdd x • (g.1 (n - x) + h.1 (n - x))))
      = (∑ x ∈ Icc f.lo (n - min g.lo h.lo),
        f.1 x * (Multiplicative.ofAdd x • (g.1 (n - x) + h.1 (n - x)))) := by
    apply sum_Icc_congr_of_vanishing
    · intro k hk
      have hz : g.1 (n - k) + h.1 (n - k) = 0 := lt_lo hk
      rw [hz, smul_zero, mul_zero]
    · intro k hk
      have h1 : g.1 (n - k) = 0 := lt_lo (lt_of_lt_of_le hk (min_le_left _ _))
      have h2 : h.1 (n - k) = 0 := lt_lo (lt_of_lt_of_le hk (min_le_right _ _))
      rw [h1, h2, add_zero, smul_zero, mul_zero]
  -- Distribute the product over the sum `g + h` coefficientwise.
  have e2 : (∑ x ∈ Icc f.lo (n - min g.lo h.lo),
        f.1 x * (Multiplicative.ofAdd x • (g.1 (n - x) + h.1 (n - x))))
      = (∑ x ∈ Icc f.lo (n - min g.lo h.lo), f.1 x * (Multiplicative.ofAdd x • g.1 (n - x)))
        + (∑ x ∈ Icc f.lo (n - min g.lo h.lo), f.1 x * (Multiplicative.ofAdd x • h.1 (n - x))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [smul_add, mul_add]
  -- Replace the common bound `min g.lo h.lo` by `g.lo` in the `g`-sum.
  have e3 : (∑ x ∈ Icc f.lo (n - min g.lo h.lo), f.1 x * (Multiplicative.ofAdd x • g.1 (n - x)))
      = (∑ x ∈ Icc f.lo (n - g.lo), f.1 x * (Multiplicative.ofAdd x • g.1 (n - x))) := by
    apply sum_Icc_congr_of_vanishing
    · intro k hk
      rw [lt_lo (lt_of_lt_of_le hk (min_le_left _ _)), smul_zero, mul_zero]
    · intro k hk
      rw [lt_lo hk, smul_zero, mul_zero]
  -- Replace the common bound `min g.lo h.lo` by `h.lo` in the `h`-sum.
  have e4 : (∑ x ∈ Icc f.lo (n - min g.lo h.lo), f.1 x * (Multiplicative.ofAdd x • h.1 (n - x)))
      = (∑ x ∈ Icc f.lo (n - h.lo), f.1 x * (Multiplicative.ofAdd x • h.1 (n - x))) := by
    apply sum_Icc_congr_of_vanishing
    · intro k hk
      rw [lt_lo (lt_of_lt_of_le hk (min_le_right _ _)), smul_zero, mul_zero]
    · intro k hk
      rw [lt_lo hk, smul_zero, mul_zero]
  rw [e1, e2, e3, e4]

end Work.ORHughesFree.SkewLaurentSeries
