/-
Auxiliary lemmas for `Work.BG.c4TripleSum` (Bender–Glauberman 1981, §4, `|S| = 4`).

Two groups of tools:

* inner-product facts for **signed irreducible** characters (`IsPmIrr`): the inner product of
  two signed irreducibles is `0`, `1` or `-1`, whence `⟨φ, ψ⟩ + star ⟨φ, ψ⟩ = 0` forces
  `⟨φ, ψ⟩ = 0` (and the analogous statements for `±2`);
* the evaluation of a `finsum` over a three-element set.

Mathlib/area BG has no packaged form of the first group (`Work.BG.inner_pmIrr_eq_pm_one`
only covers a *virtual* character of norm `1` or `2` on one side), so it is recorded here.
-/
import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_abstractCoherence

namespace Work.BG

open OddOrder.RepresentationTheory

variable {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]

/-- The inner product of two signed irreducible characters is `0`, `1` or `-1`.

`Work.BG.inner_eq_int_and_sq_le` writes `⟨φ, ψ⟩ = m` for an integer `m` with `m ^ 2 ≤ 1`
(since `⟨φ, φ⟩ = 1`), and `m ^ 2 ≤ 1` forces `m ∈ {-1, 0, 1}`. -/
theorem pmIrr_inner_eq_zero_or_one_or_neg_one {φ ψ : ClassFunction K ℂ}
    (hφ : IsPmIrr φ) (hψ : IsPmIrr ψ) :
    ClassFunction.inner φ ψ = 0 ∨ ClassFunction.inner φ ψ = 1 ∨
      ClassFunction.inner φ ψ = -1 := by
  obtain ⟨m, hm, hmle⟩ :=
    inner_eq_int_and_sq_le (IsPmIrr.mem_ZIrr hφ) 1
      (by rw [Nat.cast_one]; exact IsPmIrr.inner_self hφ) hψ
  have hm2 : m ^ 2 ≤ (1 : ℤ) := hmle
  have hle1 : m ≤ 1 := by nlinarith [sq_nonneg (m - 1), hm2]
  have hge1 : -1 ≤ m := by nlinarith [sq_nonneg (m + 1), hm2]
  have hcases : m = 0 ∨ m = 1 ∨ m = -1 := by omega
  rw [hm]
  rcases hcases with h | h | h
  · left; rw [h]; norm_num
  · right; left; rw [h]; norm_num
  · right; right; rw [h]; norm_num

/-- For signed irreducibles, `⟨φ, ψ⟩ + star ⟨φ, ψ⟩ = 0` forces `⟨φ, ψ⟩ = 0`. -/
theorem pmIrr_inner_eq_zero_of_add_star_eq_zero {φ ψ : ClassFunction K ℂ}
    (hφ : IsPmIrr φ) (hψ : IsPmIrr ψ)
    (h : ClassFunction.inner φ ψ + star (ClassFunction.inner φ ψ) = 0) :
    ClassFunction.inner φ ψ = 0 := by
  rcases pmIrr_inner_eq_zero_or_one_or_neg_one hφ hψ with h0 | h1 | h1
  · exact h0
  · rw [h1] at h; norm_num at h
  · rw [h1] at h; norm_num at h

/-- For signed irreducibles, `⟨φ, ψ⟩ + star ⟨φ, ψ⟩ = 2` forces `⟨φ, ψ⟩ = 1`. -/
theorem pmIrr_inner_eq_one_of_add_star_eq_two {φ ψ : ClassFunction K ℂ}
    (hφ : IsPmIrr φ) (hψ : IsPmIrr ψ)
    (h : ClassFunction.inner φ ψ + star (ClassFunction.inner φ ψ) = 2) :
    ClassFunction.inner φ ψ = 1 := by
  rcases pmIrr_inner_eq_zero_or_one_or_neg_one hφ hψ with h0 | h1 | h1
  · rw [h0] at h; norm_num at h
  · exact h1
  · rw [h1] at h; norm_num at h

/-- For signed irreducibles, `⟨φ, ψ⟩ + star ⟨φ, ψ⟩ = -2` forces `⟨φ, ψ⟩ = -1`. -/
theorem pmIrr_inner_eq_neg_one_of_add_star_eq_neg_two {φ ψ : ClassFunction K ℂ}
    (hφ : IsPmIrr φ) (hψ : IsPmIrr ψ)
    (h : ClassFunction.inner φ ψ + star (ClassFunction.inner φ ψ) = -2) :
    ClassFunction.inner φ ψ = -1 := by
  rcases pmIrr_inner_eq_zero_or_one_or_neg_one hφ hψ with h0 | h1 | h1
  · rw [h0] at h; norm_num at h
  · rw [h1] at h; norm_num at h
  · exact h1

/-- Evaluation of a `finsum` over a three-element set (no diamond conjunction needed). -/
theorem c4TripleAux_finsum_mem_three {α M : Type} [AddCommMonoid M] (a b c : α) (f : α → M)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ᶠ i ∈ ({a, b, c} : Set α), f i) = f a + f b + f c := by
  rw [show ({a, b, c} : Set α) = insert a (insert b {c}) from rfl,
    finsum_mem_insert _ (by simp [hab, hac])
      ((Set.finite_insert).mpr (Set.finite_singleton _)),
    finsum_mem_insert _ (by simp [hbc]) (Set.finite_singleton _),
    finsum_mem_singleton]
  abel

end Work.BG
