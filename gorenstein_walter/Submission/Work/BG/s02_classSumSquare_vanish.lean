import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_classSumSquare

namespace Work.BG

open OddOrder.RepresentationTheory

/-- An irreducible character has nonzero value at `1` (its degree is positive); hence so has
its negative. -/
theorem pmIrr_apply_one_ne_zero {K : Type} [Group K] [Fintype K]
    {θ : ClassFunction K ℂ} (h : IsPmIrr θ) : θ 1 ≠ 0 := by
  rcases h with h | h
  · obtain ⟨n, hnpos, hn, -⟩ := h.exists_natDegree_charValue_one_dvd_card
    rw [hn]
    exact_mod_cast hnpos.ne'
  · obtain ⟨n, hnpos, hn, -⟩ := h.exists_natDegree_charValue_one_dvd_card
    intro hzero
    exact hnpos.ne' (by
      have : (n : ℂ) = 0 := by rw [← hn, ClassFunction.neg_apply, hzero, neg_zero]
      exact_mod_cast this)

/-- **Vanishing form of BG Lemma 2.2-a.**  If `X` is a conjugation-invariant `Finset` of a
finite group `K`, `θ ∈ ±Irr(K)` and `θ` vanishes on `X`, then the double sum
`Σ_{x,y ∈ X} θ(x*y)` vanishes.  Immediate from `Work.BG.ClassSumSquareProp`
(`Work.BG.s02_classSumSquare`): `θ 1 * Σ θ(xy) = (Σ_{x ∈ X} θ x)² = 0` and `θ 1 ≠ 0`
(an irreducible character has positive degree,
`OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card`). -/
theorem s02_classSumSquare_vanish {K : Type} [Group K] [Fintype K] (X : Finset K)
    (hX : ∀ g x : K, x ∈ X → g * x * g⁻¹ ∈ X)
    (θ : OddOrder.RepresentationTheory.ClassFunction K ℂ) (hθ : Work.BG.IsPmIrr θ)
    (h0 : ∀ x ∈ X, θ x = 0) :
    ∑ x ∈ X, ∑ y ∈ X, θ (x * y) = 0 := by
  have hsq := Work.BG.s02_classSumSquare X hX θ hθ
  have hsum : (∑ x ∈ X, θ x) = 0 := Finset.sum_eq_zero fun x hx => h0 x hx
  have hsq' : θ 1 * (∑ x ∈ X, ∑ y ∈ X, θ (x * y)) = 0 := by
    simpa only [hsum, sq, mul_zero] using hsq
  exact (mul_eq_zero.mp hsq').resolve_left (pmIrr_apply_one_ne_zero hθ)

end Work.BG
