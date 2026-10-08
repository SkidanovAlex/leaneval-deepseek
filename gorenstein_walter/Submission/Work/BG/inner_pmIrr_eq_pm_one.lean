import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_abstractCoherence

namespace Work.BG

open OddOrder.RepresentationTheory

/-- An integer whose square is at most `2` and which is nonzero is `±1`. -/
private theorem int_eq_pm_one_of_sq_le_two {m : ℤ} (hbound : m ^ 2 ≤ 2) (hne : m ≠ 0) :
    m = 1 ∨ m = -1 := by
  have hge : (1 : ℤ) ≤ m ^ 2 := by
    have h : (1 : ℤ) ≤ |m| := Int.one_le_abs hne
    have hs := sq_abs m
    nlinarith
  have hne2 : m ^ 2 ≠ 2 := by
    intro hh
    have h1 : (m - 1) * (m + 1) = 1 := by linear_combination hh
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have h2 : m ^ 2 = 1 := by omega
  rw [pow_two] at h2
  exact mul_self_eq_one_iff.mp h2

/-- **BG: the inner product of a signed irreducible with a virtual character of norm `1` or `2`
is `±1` whenever it is nonzero.**

`φ ∈ ℤ[Irr G]` has `‖φ‖² = N ∈ {1, 2}`.  By `Work.BG.inner_eq_int_and_sq_le` the Fourier
coefficient `m = ⟨φ, χ⟩` of a signed irreducible `χ` is an integer with `m² ≤ N ≤ 2`.  The
inner product is conjugate-symmetric (`⟨χ, φ⟩ = star ⟨φ, χ⟩`, and the value is a real integer),
so the hypothesis `⟨χ, φ⟩ ≠ 0` forces `m ≠ 0`; the integer `m` with `1 ≤ m² ≤ 2` and `m² ≠ 2`
satisfies `m = ±1`, and `⟨χ, φ⟩ = star m = m`. -/
theorem inner_pmIrr_eq_pm_one {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {φ χ : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hφ : φ ∈ OddOrder.RepresentationTheory.ZIrr G)
    (hnorm : OddOrder.RepresentationTheory.ClassFunction.inner φ φ = 1 ∨
      OddOrder.RepresentationTheory.ClassFunction.inner φ φ = 2)
    (hχ : Work.BG.IsPmIrr χ)
    (hne : OddOrder.RepresentationTheory.ClassFunction.inner χ φ ≠ 0) :
    OddOrder.RepresentationTheory.ClassFunction.inner χ φ = 1 ∨
      OddOrder.RepresentationTheory.ClassFunction.inner χ φ = -1 := by
  have key : ∀ N : ℕ, ClassFunction.inner φ φ = (N : ℂ) → (N : ℤ) ≤ 2 →
      ClassFunction.inner χ φ = 1 ∨ ClassFunction.inner χ φ = -1 := by
    intro N hN hNle
    obtain ⟨m, hm, hmle⟩ := inner_eq_int_and_sq_le hφ N hN hχ
    have hχφ : ClassFunction.inner χ φ = (m : ℂ) := by
      have h := ClassFunction.inner_star_comm (G := G) χ φ
      rw [hm, star_intCast] at h
      exact h
    have hmne : m ≠ 0 := fun h0 => hne (by rw [hχφ, h0]; simp)
    have hbound : m ^ 2 ≤ 2 := le_trans hmle hNle
    rcases int_eq_pm_one_of_sq_le_two hbound hmne with h | h
    · left; rw [hχφ, h]; norm_num
    · right; rw [hχφ, h]; norm_num
  rcases hnorm with h | h
  · exact key 1 (by simpa using h) (by norm_num)
  · exact key 2 (by simpa using h) (by norm_num)

end Work.BG
