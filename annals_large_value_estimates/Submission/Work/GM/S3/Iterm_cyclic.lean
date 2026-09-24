import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs

/-!
# Cyclic symmetry of `Iterm` (GM Lemma 4.5)

`Submission.GM.Iterm N W m` is the triple sum
`N³ Σ_{t₁,t₂,t₃ ∈ W} ĥ_{t₁-t₂}(m₁N) ĥ_{t₂-t₃}(m₂N) ĥ_{t₃-t₁}(m₃N)`.

It is invariant under the cyclic permutation `(m₁,m₂,m₃) ↦ (m₂,m₃,m₁)` of the
frequency triple: the cyclic shift of the summation variables `(t₁,t₂,t₃) ↦ (t₂,t₃,t₁)`
is a bijection of `W × W × W` and turns the summand into a permutation of the three
factors of the summand defining `Iterm N W (m₁,m₂,m₃)`.

The combinatorial content is isolated in `sum_cyclic_three`: a triple sum over a
finset is invariant under the cyclic rotation of its summation variables.
-/

open Complex Finset
open scoped BigOperators

namespace Work.GM.S3

open Submission.GM (Iterm hhat)

/-- A triple sum over a finset is invariant under the cyclic rotation
`(a,b,c) ↦ (b,c,a)` of its summation variables.

This is a reindexing statement: the map `(a,b,c) ↦ (b,c,a)` is a bijection of the
cube `s × s × s`, so it only permutes the terms of the sum.  It is proved by
converting the iterated sum into a sum over the product finset `s ×ˢ (s ×ˢ s)` and
applying `Finset.sum_nbij'` with that bijection (whose inverse is
`(a,b,c) ↦ (c,a,b)`). -/
theorem sum_cyclic_three {α M : Type*} [AddCommMonoid M] (s : Finset α)
    (f : α → α → α → M) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a b c) = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f b c a := by
  have hL : (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a b c)
      = ∑ p ∈ s ×ˢ (s ×ˢ s), f p.1 p.2.1 p.2.2 := by
    simp only [Finset.sum_product]
  have hR : (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f b c a)
      = ∑ p ∈ s ×ˢ (s ×ˢ s), f p.2.1 p.2.2 p.1 := by
    simp only [Finset.sum_product]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun p : α × (α × α) => (p.2.2, (p.1, p.2.1)))
    (fun p : α × (α × α) => (p.2.1, (p.2.2, p.1))) ?_ ?_ ?_ ?_ ?_
  · intro p hp; simp only [Finset.mem_product] at hp ⊢; exact ⟨hp.2.2, hp.1, hp.2.1⟩
  · intro p hp; simp only [Finset.mem_product] at hp ⊢; exact ⟨hp.2.1, hp.2.2, hp.1⟩
  · intro p hp; rfl
  · intro p hp; rfl
  · intro p hp; rfl

/-- `Iterm` is invariant under the cyclic permutation of its frequency triple:
`Iterm N W (m₂,m₃,m₁) = Iterm N W (m₁,m₂,m₃)`. -/
theorem Iterm_cyclic (N : ℕ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ) :
    Submission.GM.Iterm N W (m₂, m₃, m₁) = Submission.GM.Iterm N W (m₁, m₂, m₃) := by
  simp only [Submission.GM.Iterm]
  congr 1
  rw [sum_cyclic_three]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  ring

end Work.GM.S3
