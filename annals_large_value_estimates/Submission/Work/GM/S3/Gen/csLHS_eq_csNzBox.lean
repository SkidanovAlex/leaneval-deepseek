import Mathlib
import Submission.Work.GM.S3.Gen.cs_defs

/-!
# `csLHS_eq_csNzBox`

`csLHS N δ W` (the left hand side of `S3_le_cellSum`) is the triple sum over the truncated cube
`Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋³`, restricted by an `if` to the triples all of whose coordinates are
nonzero.  Since `csNzBox (Klev N δ)` is by definition the product of the three *filtered* intervals,
the two expressions are the same sum written in two ways: both equal the iterated sum of the
`if`-expression `if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then ‖Iterm N W (m₁,m₂,m₃)‖ else 0`.

The three private lemmas below are the bookkeeping: pulling a propositional `if` out of a finite
sum, splitting a conjunction of three conditions in an `if`, and rewriting a sum over a triple
product of finsets as an iterated sum.
-/

namespace Work.GM.S3.Gen

open Finset
open scoped BigOperators

noncomputable section

/-- Pulling a propositional `if` out of a finite sum. -/
private lemma sum_ite_const {α : Type*} {s : Finset α} (p : Prop) [Decidable p] (g : α → ℝ) :
    (∑ b ∈ s, if p then g b else 0) = if p then ∑ b ∈ s, g b else 0 := by
  by_cases h : p <;> simp [h]

/-- Splitting a conjunction of three propositions in the condition of an `if`. -/
private lemma ite_and_and (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] (x : ℝ) :
    (if p ∧ q ∧ r then x else 0) = if p then (if q then (if r then x else 0) else 0) else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr]

/-- The sum over a product of three finsets of integers, as an iterated sum. -/
private lemma sum_product3_eq (A B C : Finset ℤ) (g : ℤ × ℤ × ℤ → ℝ) :
    (∑ u ∈ A.product (B.product C), g u) = ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, g (a, b, c) := by
  rw [show (@Finset.product ℤ (ℤ × ℤ) A (B.product C)) = A ×ˢ (B ×ˢ C) from rfl]
  simp only [Finset.sum_product]

theorem csLHS_eq_csNzBox (N : ℕ) (δ : ℝ) (W : Finset ℝ) :
    Work.GM.S3.Gen.csLHS N δ W =
      ∑ u ∈ Work.GM.S3.Gen.csNzBox (Work.GM.S3.Gen.Klev N δ),
        ‖Submission.GM.Iterm N W u‖ := by
  rw [Work.GM.S3.Gen.csLHS, Work.GM.S3.Gen.csNzBox, sum_product3_eq]
  -- the right hand side is now an iterated sum over the three filtered intervals;
  -- turn each filtered sum into a sum with an `if`
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← sum_ite_const (s := Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋)
    (p := a ≠ 0)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← sum_ite_const (s := Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋)
    (p := b ≠ 0)]
  rw [← sum_ite_const (s := Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋)
    (p := a ≠ 0)]
  exact Finset.sum_congr rfl
    (fun c _ => ite_and_and (a ≠ 0) (b ≠ 0) (c ≠ 0) (‖Submission.GM.Iterm N W (a, b, c)‖))

end

end Work.GM.S3.Gen
