import Mathlib
import Submission.Work.GM.S3.Gen.cs_defs
import Submission.Work.GM.S3.Iterm_cyclic
import Submission.Work.GM.S3.Gen.truncsum_le_Lambda

/-!
# `Σ_{csNzBox} ‖I_m‖ ≤ 3 Σ_{csMaxBox} ‖I_m‖`

The truncated nonzero cube `csNzBox K` is the product of the three copies of
`(Icc (-⌊K⌋) ⌊K⌋).filter (· ≠ 0)`, and `csMaxBox K` is its part on which the *second*
coordinate has the largest modulus (GM's `Λ`).  This is the `csNzBox`-form of
`Work.GM.S3.Gen.truncsum_le_Lambda`: the latter is stated as an iterated sum over `Icc`
with `if`-indicators, and the three lemmas below translate between the two presentations
(`csBox_sum_prod3`: product → iterated sum, `csBox_sum3_filter`: the `≠ 0` filters →
indicators, `csBox_sum_csNzBox_eq` / `csBox_sum_csMaxBox_eq`: the two finsets above).

The mathematics is entirely in `truncsum_le_Lambda` (the three norm-symmetries
`norm_Iterm_swap12`, `norm_Iterm_swap23` of `Iterm` together with "one of three reals is a
maximum"); here we only change the presentation of the two sums.
-/

namespace Work.GM.S3.Gen

open Finset
open scoped BigOperators

/-- A sum over the triple product `A × A × A` is an iterated sum. -/
lemma csBox_sum_prod3 (A : Finset ℤ) (F : ℤ × ℤ × ℤ → ℝ) :
    (∑ u ∈ A.product (A.product A), F u) = ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A, F (a, b, c) := by
  trans ∑ a ∈ A, ∑ bc ∈ A.product A, F (a, bc)
  · exact Finset.sum_product A (A.product A) F
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    trans ∑ b ∈ A, ∑ c ∈ A, F (a, (b, c))
    · exact Finset.sum_product A A (fun bc => F (a, bc))
    · rfl

/-- An iterated sum over the three copies of `A.filter p` is the iterated sum over `A` of
the `p`-indicator. -/
lemma csBox_sum3_filter (A : Finset ℤ) (p : ℤ → Prop) [DecidablePred p] (F : ℤ × ℤ × ℤ → ℝ) :
    (∑ a ∈ A.filter p, ∑ b ∈ A.filter p, ∑ c ∈ A.filter p, F (a, b, c))
      = ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A, (if p a ∧ p b ∧ p c then F (a, b, c) else 0) := by
  trans ∑ a ∈ A, if p a then (∑ b ∈ A.filter p, ∑ c ∈ A.filter p, F (a, b, c)) else 0
  · exact Finset.sum_filter p (fun a => ∑ b ∈ A.filter p, ∑ c ∈ A.filter p, F (a, b, c))
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : p a
  · rw [if_pos ha]
    trans ∑ b ∈ A, if p b then (∑ c ∈ A.filter p, F (a, b, c)) else 0
    · exact Finset.sum_filter p (fun b => ∑ c ∈ A.filter p, F (a, b, c))
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : p b
    · rw [if_pos hb]
      trans ∑ c ∈ A, if p c then F (a, b, c) else 0
      · exact Finset.sum_filter p (fun c => F (a, b, c))
      refine Finset.sum_congr rfl (fun c _ => ?_)
      by_cases hc : p c <;> simp [ha, hb, hc]
    · rw [if_neg hb]
      simp [ha, hb]
  · rw [if_neg ha]
    simp [ha]

/-- The sum over the truncated nonzero cube, as an iterated sum with indicator. -/
lemma csBox_sum_csNzBox_eq (K : ℝ) (F : ℤ × ℤ × ℤ → ℝ) :
    (∑ u ∈ csNzBox K, F u) =
      ∑ m₁ ∈ Finset.Icc (-⌊K⌋) ⌊K⌋, ∑ m₂ ∈ Finset.Icc (-⌊K⌋) ⌊K⌋,
      ∑ m₃ ∈ Finset.Icc (-⌊K⌋) ⌊K⌋,
        (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then F (m₁, m₂, m₃) else 0) := by
  have hbox : csNzBox K = ((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0)).product
      (((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0)).product
        ((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0))) := rfl
  rw [hbox, csBox_sum_prod3, csBox_sum3_filter]

/-- The sum over the `Λ`-part of the truncated nonzero cube (second coordinate of maximal
modulus), as an iterated sum with indicator. -/
lemma csBox_sum_csMaxBox_eq (K : ℝ) (F : ℤ × ℤ × ℤ → ℝ) :
    (∑ u ∈ csMaxBox K, F u) =
      ∑ m₁ ∈ Finset.Icc (-⌊K⌋) ⌊K⌋, ∑ m₂ ∈ Finset.Icc (-⌊K⌋) ⌊K⌋,
      ∑ m₃ ∈ Finset.Icc (-⌊K⌋) ⌊K⌋,
        (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 ∧ |(m₁ : ℝ)| ≤ |(m₂ : ℝ)| ∧ |(m₃ : ℝ)| ≤ |(m₂ : ℝ)|
          then F (m₁, m₂, m₃) else 0) := by
  have hmax : csMaxBox K = (((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0)).product
      (((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0)).product
        ((Finset.Icc (-⌊K⌋) ⌊K⌋).filter (fun m : ℤ => m ≠ 0)))).filter
      (fun u : ℤ × ℤ × ℤ => |(u.1 : ℝ)| ≤ |(u.2.1 : ℝ)| ∧ |(u.2.2 : ℝ)| ≤ |(u.2.1 : ℝ)|) := rfl
  rw [hmax, Finset.sum_filter]
  trans ∑ a ∈ Finset.Icc (-⌊K⌋) ⌊K⌋, ∑ b ∈ Finset.Icc (-⌊K⌋) ⌊K⌋,
      ∑ c ∈ Finset.Icc (-⌊K⌋) ⌊K⌋,
      (if a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 then
        (if |(a : ℝ)| ≤ |(b : ℝ)| ∧ |(c : ℝ)| ≤ |(b : ℝ)| then F (a, b, c) else 0) else 0)
  · exact csBox_sum_csNzBox_eq K
      (fun u => if |(u.1 : ℝ)| ≤ |(u.2.1 : ℝ)| ∧ |(u.2.2 : ℝ)| ≤ |(u.2.1 : ℝ)|
        then F u else 0)
  · refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => ?_)))
    by_cases h : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 <;>
      by_cases hq : |(a : ℝ)| ≤ |(b : ℝ)| ∧ |(c : ℝ)| ≤ |(b : ℝ)| <;> simp [h, hq]

theorem csNzBox_le_three_maxBox (K : ℝ) (N : ℕ) (W : Finset ℝ) :
    (∑ u ∈ Work.GM.S3.Gen.csNzBox K, ‖Submission.GM.Iterm N W u‖) ≤
      3 * ∑ u ∈ Work.GM.S3.Gen.csMaxBox K, ‖Submission.GM.Iterm N W u‖ := by
  rw [csBox_sum_csNzBox_eq K (fun u => ‖Submission.GM.Iterm N W u‖),
      csBox_sum_csMaxBox_eq K (fun u => ‖Submission.GM.Iterm N W u‖)]
  exact truncsum_le_Lambda N W K

end Work.GM.S3.Gen
