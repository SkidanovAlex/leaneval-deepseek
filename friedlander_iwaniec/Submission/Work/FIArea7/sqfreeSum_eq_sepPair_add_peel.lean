import Mathlib
import Submission.Work.FIArea7.SepDiv
import Submission.Work.FIArea7.sum_eq_sepPairSum
import Submission.Work.FIArea7.sum_sqfree_peel

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section
open Classical

/-- The predicate defining the "squarefree small-prime" range `ℓ ⩽ X` with all prime factors
`⩽ z`: this is the common index set of `sqfreeSum`, `sepSumLHS` and `sepPairSum`. -/
def sqfreeCond (X z l : ℕ) : Prop := Squarefree l ∧ l ≤ X ∧ ∀ p, p.Prime → p ∣ l → p ≤ z

/-- The "squarefree small-prime" part of `f`: `f` cut down to the numbers that are squarefree,
`≤ X`, and all of whose prime factors are `≤ z`. -/
def sqfreeTrunc (X z : ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun l => if sqfreeCond X z l then f l else 0

/-- The truncation never produces a value outside the squarefree small-prime range. -/
lemma sqfreeTrunc_ne_zero {X z : ℕ} {f : ℕ → ℂ} {l : ℕ} (h : sqfreeTrunc X z f l ≠ 0) :
    sqfreeCond X z l := by
  by_contra hc
  exact h (by unfold sqfreeTrunc; rw [if_neg hc])

/-- `sepSumLHS` is insensitive to the truncation. -/
lemma sepSumLHS_sqfreeTrunc (X z : ℕ) (f : ℕ → ℂ) :
    sepSumLHS X z (sqfreeTrunc X z f) = sepSumLHS X z f := by
  unfold sepSumLHS
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_filter, Finset.mem_Icc] at hl
  obtain ⟨⟨hl1, hlX⟩, hsq, hQ⟩ := hl
  have hc : sqfreeCond X z l := ⟨hsq, hlX, hQ⟩
  unfold sqfreeTrunc
  rw [if_pos hc]

/-- `sepPairSum` is insensitive to the truncation, because a triple with product `> X` has
`f`-value `0` by the support hypothesis `hsupp`. -/
lemma sepPairSum_sqfreeTrunc (r D X z : ℕ) (f : ℕ → ℂ)
    (hsupp : ∀ l, f l ≠ 0 → l ≤ X) :
    sepPairSum r D X z (sqfreeTrunc X z f) = sepPairSum r D X z f := by
  unfold sepPairSum
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hcond : IsSepPair r d m n ∧ (∀ p, p.Prime → p ∣ d * m * n → p ≤ z)
  · rw [if_pos hcond, if_pos hcond]
    by_cases hle : d * m * n ≤ X
    · have hc : sqfreeCond X z (d * m * n) := ⟨sepPair_squarefree hcond.1, hle, hcond.2⟩
      unfold sqfreeTrunc
      rw [if_pos hc]
    · have hz : f (d * m * n) = 0 := by
        by_contra hf
        exact hle (hsupp (d * m * n) hf)
      have hc : ¬ sqfreeCond X z (d * m * n) := fun h => hle h.2.1
      unfold sqfreeTrunc
      rw [if_neg hc, hz]
  · rw [if_neg hcond, if_neg hcond]

theorem sqfreeSum_eq_sepPair_add_peel (r X z D : ℕ) (hr : 2 ≤ r) (f : ℕ → ℂ)
    (hsupp : ∀ l, f l ≠ 0 → l ≤ X)
    (hD : ∀ l d m n, Squarefree l → l ≤ X → (∀ p, p.Prime → p ∣ l → p ≤ z) →
            IsSepPair r d m n → d * m * n = l → d ≤ D) :
    sqfreeSum X f = sepPairSum r D X z f + peelSum X z f := by
  have hkey : sepSumLHS X z f = sepPairSum r D X z f := by
    rw [← sepSumLHS_sqfreeTrunc X z f, ← sepPairSum_sqfreeTrunc r D X z f hsupp]
    exact sum_eq_sepPairSum r X z D hr (sqfreeTrunc X z f)
      (fun l hl => by
        obtain ⟨h1, h2, h3⟩ := sqfreeTrunc_ne_zero hl
        exact ⟨h1, h2, h3⟩) hD
  rw [sum_sqfree_peel X z f, hkey]

end

end Work.FIArea7
