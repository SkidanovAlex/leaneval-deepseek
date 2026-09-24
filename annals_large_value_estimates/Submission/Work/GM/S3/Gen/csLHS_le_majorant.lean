import Mathlib
import Submission.Work.GM.S3.Gen.cs_defs

namespace Work.GM.S3.Gen

open Finset
open scoped BigOperators

/-- The triple product sum factors as the cube of the plain sum (for a commutative ring). -/
lemma csLHS_sum_cube_factor (s : Finset ℤ) (f : ℤ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c) = (∑ x ∈ s, f x) ^ 3 := by
  have hSS : (∑ x ∈ s, f x) * (∑ x ∈ s, f x) = ∑ a ∈ s, ∑ b ∈ s, f a * f b :=
    Finset.sum_mul_sum s s f f
  have h1 : (∑ a ∈ s, ∑ b ∈ s, f a * f b) * (∑ c ∈ s, f c)
      = ∑ a ∈ s, ∑ c ∈ s, ∑ b ∈ s, f a * f b * f c := by
    rw [Finset.sum_mul_sum s s (fun a => ∑ b ∈ s, f a * f b) f]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.sum_mul]
  have h2 : (∑ a ∈ s, ∑ c ∈ s, ∑ b ∈ s, f a * f b * f c)
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c := by
    apply Finset.sum_congr rfl; intro a _
    exact Finset.sum_comm
  rw [← h2, ← h1]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, hSS]

/-- Fubini for the triple sum with a constant factor pulled out. -/
lemma csLHS_const_factor (s : Finset ℤ) (C : ℝ) (f : ℤ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, C * (f a * f b * f c))
      = C * (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c) := by
  simp only [Finset.mul_sum]

/-- The truncated triple sum `csLHS` is bounded by the cube of any one-dimensional
majorant sum, provided the majorant bounds `‖Iterm‖` coordinatewise. -/
theorem csLHS_le_majorant (N : ℕ) (δ : ℝ) (W : Finset ℝ) (bnd : ℤ → ℝ) (hbnd : ∀ m, 0 ≤ bnd m)
    (h : ∀ (m : ℤ × ℤ × ℤ), m.1 ≠ 0 → m.2.1 ≠ 0 → m.2.2 ≠ 0 →
        ‖Submission.GM.Iterm N W m‖ ≤
          (N:ℝ)^3 * (W.card:ℝ)^3 * (bnd m.1 * bnd m.2.1 * bnd m.2.2)) :
    Work.GM.S3.Gen.csLHS N δ W ≤ (N:ℝ)^3 * (W.card:ℝ)^3 *
      (∑ m ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋, bnd m)^3 := by
  have hpt : ∀ m₁ m₂ m₃ : ℤ,
      (if (m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0) then
          ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ else 0)
        ≤ (N:ℝ)^3 * (W.card:ℝ)^3 * (bnd m₁ * bnd m₂ * bnd m₃) := by
    intro m₁ m₂ m₃
    by_cases hP : m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0
    · rw [if_pos hP]
      exact h (m₁, m₂, m₃) hP.1 hP.2.1 hP.2.2
    · rw [if_neg hP]
      have hb : 0 ≤ bnd m₁ * bnd m₂ * bnd m₃ :=
        mul_nonneg (mul_nonneg (hbnd m₁) (hbnd m₂)) (hbnd m₃)
      have hN3 : (0:ℝ) ≤ (N:ℝ)^3 := by positivity
      have hW3 : (0:ℝ) ≤ (W.card:ℝ)^3 := by positivity
      exact mul_nonneg (mul_nonneg hN3 hW3) hb
  have hsum : Work.GM.S3.Gen.csLHS N δ W ≤
      ∑ m₁ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
        ∑ m₂ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
          ∑ m₃ ∈ Finset.Icc (-⌊Work.GM.S3.Gen.Klev N δ⌋) ⌊Work.GM.S3.Gen.Klev N δ⌋,
            (N:ℝ)^3 * (W.card:ℝ)^3 * (bnd m₁ * bnd m₂ * bnd m₃) := by
    unfold Work.GM.S3.Gen.csLHS
    apply Finset.sum_le_sum; intro m₁ _
    apply Finset.sum_le_sum; intro m₂ _
    apply Finset.sum_le_sum; intro m₃ _
    exact hpt m₁ m₂ m₃
  refine hsum.trans (le_of_eq ?_)
  rw [csLHS_const_factor, csLHS_sum_cube_factor]

end Work.GM.S3.Gen
