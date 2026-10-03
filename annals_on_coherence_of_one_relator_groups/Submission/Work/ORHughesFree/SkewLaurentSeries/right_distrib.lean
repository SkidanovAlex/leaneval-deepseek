import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.left_distrib

open Finset

namespace Work.ORHughesFree.SkewLaurentSeries

/-- Two `Icc` sums with a common upper bound `Nu` and lower bounds `L₁`, `L₂` agree as soon as
the summand vanishes below *both* candidate lower bounds.  Companion of
`sum_Icc_congr_of_vanishing` for the lower boundary: it lets us replace the arbitrary
`Classical.choose` bound `lo` of an element (e.g. of `f + g`) by an explicit valid lower bound. -/
theorem sum_Icc_congr_lower {B : Type*} [AddCommMonoid B] (w : ℤ → B)
    (Nu L₁ L₂ : ℤ) (h₁ : ∀ k : ℤ, k < L₁ → w k = 0)
    (h₂ : ∀ k : ℤ, k < L₂ → w k = 0) :
    (∑ k ∈ Finset.Icc L₁ Nu, w k) = ∑ k ∈ Finset.Icc L₂ Nu, w k := by
  rcases le_total L₁ L₂ with hle | hle
  · symm
    apply Finset.sum_subset (s₁ := Finset.Icc L₂ Nu) (s₂ := Finset.Icc L₁ Nu)
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      exact ⟨by omega, hx.2⟩
    · intro x hx hxs
      simp only [Finset.mem_Icc] at hx hxs
      have hxlt : x < L₂ := by
        by_contra hcon
        exact hxs ⟨by omega, hx.2⟩
      exact h₂ x hxlt
  · apply Finset.sum_subset (s₁ := Finset.Icc L₁ Nu) (s₂ := Finset.Icc L₂ Nu)
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      exact ⟨by omega, hx.2⟩
    · intro x hx hxs
      simp only [Finset.mem_Icc] at hx hxs
      have hxlt : x < L₁ := by
        by_contra hcon
        exact hxs ⟨by omega, hx.2⟩
      exact h₁ x hxlt

theorem right_distrib {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f g h : SkewLaurentSeries A) : (f + g) * h = f * h + g * h := by
  apply Subtype.ext
  funext n
  simp only [mul_apply, add_apply]
  -- The coefficient of `(f + g) * h` at `n` is
  -- `∑ k ∈ Icc (f+g).lo (n - h.lo), (f.1 k + g.1 k) * (ofAdd k • h.1 (n - k))`.
  -- Step 1: replace the arbitrary chosen bound `(f + g).lo` by the explicit valid lower
  -- bound `min f.lo g.lo`.
  have e1 : (∑ x ∈ Icc (f + g).lo (n - h.lo),
        (f.1 x + g.1 x) * (Multiplicative.ofAdd x • h.1 (n - x)))
      = (∑ x ∈ Icc (min f.lo g.lo) (n - h.lo),
        (f.1 x + g.1 x) * (Multiplicative.ofAdd x • h.1 (n - x))) := by
    apply sum_Icc_congr_lower
    · intro k hk
      have hz : f.1 k + g.1 k = 0 := lt_lo hk
      rw [hz, zero_mul]
    · intro k hk
      have h1 : f.1 k = 0 := lt_lo (lt_of_lt_of_le hk (min_le_left _ _))
      have h2 : g.1 k = 0 := lt_lo (lt_of_lt_of_le hk (min_le_right _ _))
      rw [h1, h2, add_zero, zero_mul]
  -- Step 2: distribute the coefficientwise product over the sum `f.1 k + g.1 k`.
  have e2 : (∑ x ∈ Icc (min f.lo g.lo) (n - h.lo),
        (f.1 x + g.1 x) * (Multiplicative.ofAdd x • h.1 (n - x)))
      = (∑ x ∈ Icc (min f.lo g.lo) (n - h.lo),
          f.1 x * (Multiplicative.ofAdd x • h.1 (n - x)))
        + (∑ x ∈ Icc (min f.lo g.lo) (n - h.lo),
          g.1 x * (Multiplicative.ofAdd x • h.1 (n - x))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [add_mul]
  -- Step 3: replace the common bound `min f.lo g.lo` by `f.lo` in the `f`-sum.
  have e3 : (∑ x ∈ Icc (min f.lo g.lo) (n - h.lo),
        f.1 x * (Multiplicative.ofAdd x • h.1 (n - x)))
      = (∑ x ∈ Icc f.lo (n - h.lo),
        f.1 x * (Multiplicative.ofAdd x • h.1 (n - x))) := by
    apply sum_Icc_congr_lower
    · intro k hk
      rw [lt_lo (lt_of_lt_of_le hk (min_le_left _ _)), zero_mul]
    · intro k hk
      rw [lt_lo hk, zero_mul]
  -- Step 4: replace the common bound `min f.lo g.lo` by `g.lo` in the `g`-sum.
  have e4 : (∑ x ∈ Icc (min f.lo g.lo) (n - h.lo),
        g.1 x * (Multiplicative.ofAdd x • h.1 (n - x)))
      = (∑ x ∈ Icc g.lo (n - h.lo),
        g.1 x * (Multiplicative.ofAdd x • h.1 (n - x))) := by
    apply sum_Icc_congr_lower
    · intro k hk
      rw [lt_lo (lt_of_lt_of_le hk (min_le_right _ _)), zero_mul]
    · intro k hk
      rw [lt_lo hk, zero_mul]
  rw [e1, e2, e3, e4]

end Work.ORHughesFree.SkewLaurentSeries
