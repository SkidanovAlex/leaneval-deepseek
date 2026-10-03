/-
# The support of the randomised small-scale symbol `randSymb (smallSymbF …) ε K`

The randomised symbol of §7 is the finite combination of the modulated Ionescu--Wainger bumps

  `randSymb φ ε K ξ = ∑_{n < K} ε n · (φ (n+1) ξ - φ n ξ)`

with `φ = smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t`, where

  `smallSymbF … m ξ = if m ≠ 0 ∧ smallCond … m then φ_{N_m,t}(ξ) else 0`,  `N_m = ⌊a m⌋`

(`randSymbDefs.smallSymbF_apply`), and `φ_{N,t}` is the modulated bump of §6.

Since the bumps `φ_{N,t}` are supported in the band `|ξ| ≤ 2^{k₁ - Log N}`
(`narrow_of_core.varphiNt_support_le_all`, valid at every height `k₁ ≥ 0`), a nonzero value of the
*sum* `randSymb … ξ` forces one of its summands to be nonzero, hence one of the two values
`φ_{N_m,t}(ξ)` at the indices `m = n` and `m = n+1` of that summand to be nonzero; at that index
`smallCond` holds, so the support bound and the hypothesis `hR` combine to give `|ξ| ≤ R`.

This is the statement that lets the symbol `randSymb (smallSymbF …) ε K` be regarded as a Fourier
multiplier supported in the band `|ξ| ≤ R`, *uniformly* in the truncation `K` and in the signs
`ε` (no hypothesis on `ε` beyond what the caller has is needed here).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymbDefs
import Submission.Work.KMTAreas.A7.narrow_of_core

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open Finset

/-! ## The bridge between the real and the integer exponent -/

/-- **The exponent `k - Log N` of the support bound, as the cast of an integer.**  The support
bound `varphiNt_support_le_all` is phrased with the *real* exponent `(k : ℝ) - (Log N : ℝ)`
(so that the powers are `Real.rpow`), while the hypothesis `hR` of `randSymb_support_le` is
phrased with the *integer* exponent `(k : ℤ) - Log N` (`zpow`); this is the equality that lets the
two be compared. -/
lemma rpow_two_sub_logN (k N : ℕ) :
    (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) =
      (2 : ℝ) ^ ((k : ℤ) - Work.Analysis.EndVar.logN N) := by
  rw [← Real.rpow_intCast (2 : ℝ) ((k : ℤ) - Work.Analysis.EndVar.logN N)]
  push_cast
  ring

/-! ## The support of the randomised symbol -/

theorem randSymb_support_le (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (ε : ℕ → ℂ) (K : ℕ) (R : ℝ)
    (hR : ∀ n : ℕ, Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ n →
      (2 : ℝ) ^ ((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ R) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K ξ ≠ 0
      → |ξ| ≤ R := by
  intro ξ hξ
  -- a nonzero sum has a nonzero summand
  rw [randSymb] at hξ
  obtain ⟨n, _hn, hnne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hξ
  -- the two bumps appearing in that summand are then distinct, so one of them is nonzero
  have hdiff : smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t (n + 1) ξ ≠ smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n ξ :=
    fun h => hnne (by rw [h, sub_self, mul_zero])
  have hor : smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t (n + 1) ξ ≠ 0 ∨
      smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n ξ ≠ 0 := by
    by_contra h
    push Not at h
    exact hdiff (by rw [h.1, h.2])
  -- at a nonzero index the family is the modulated bump at the lacunary scale `⌊a j⌋`, on the
  -- small-scale condition, so the support bound and the hypothesis `hR` both apply
  have aux : ∀ j : ℕ, smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t j ξ ≠ 0 → |ξ| ≤ R := by
    intro j hj
    rw [congrFun (smallSymbF_apply ρ C₀ a l₁ l₂ k₁ k₂ t j) ξ] at hj
    by_cases hr : randAct ρ C₀ a l₁ l₂ k₁ k₂ j
    · rw [if_pos hr] at hj
      refine le_trans (varphiNt_support_le_all k₁ (Nat.floor (a j)) t ξ hj) ?_
      rw [rpow_two_sub_logN k₁ (Nat.floor (a j))]
      exact hR j hr.2
    · rw [if_neg hr] at hj
      exact absurd rfl hj
  rcases hor with h | h
  · exact aux (n + 1) h
  · exact aux n h

end

end Work.KMTAreas.A7
