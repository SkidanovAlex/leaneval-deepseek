/-
# The support of the randomised `g`-side small-scale symbol `randSymb (smallSymbG …) ε K`

This is the `g`-side companion of `Work.KMTAreas.A7.randSymb_support_le`.  The randomised symbol

  `randSymb φ ε K ξ = ∑_{n < K} ε n · (φ (n+1) ξ - φ n ξ)`

with `φ = smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t` is a finite combination of the modulated `d`-fold
Ionescu–Wainger bumps `φ̃_{N,t}`, `d = P.natDegree`, at the lacunary scales `N = ⌊a n⌋`:

  `smallSymbG … m ξ = if m ≠ 0 ∧ smallCond … m then φ̃_{⌊a m⌋,t}(ξ) else 0`

(`randSymbGCoefDefs.smallSymbG_apply`).  Since a nonzero value of `φ̃_{N,t}` forces
`|ξ| ≤ 2^{d(k₂ - Log N)}` (`varphitildeNt_support_all`, valid with no regime restriction), a
nonzero value of the *sum* `randSymb … ξ` forces one of its summands to be nonzero, hence one of
the two bumps of that summand to be nonzero; at that index `smallCond` holds, so the support bound
and the hypothesis `hR` combine to give `|ξ| ≤ R`.

Consequently `randSymb (smallSymbG …) ε K` is a Fourier multiplier supported in the band
`|ξ| ≤ R`, *uniformly* in the truncation `K` and in the signs `ε`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all
import Submission.Work.KMTAreas.A7.randSymbG_aux
import Submission.Work.KMTAreas.A7.randSymbGCoefDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open Finset

/-- **The exponent `d (k - Log N)` of the support bound, as the cast of an integer.**  The support
bound `varphitildeNt_support_all` is phrased with the *real* exponent
`(d : ℝ) * ((k : ℝ) - (logN N : ℝ))` (so that the power is `Real.rpow`), while the hypothesis
`hR` of `randSymbG_support_le` is phrased with the *integer* exponent
`(d : ℤ) * ((k : ℤ) - logN N)` (`zpow`); this is the equality that lets the two be compared. -/
lemma rpow_natDegree_sub_logN (d k N : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) =
      (2 : ℝ) ^ ((d : ℤ) * ((k : ℤ) - Work.Analysis.EndVar.logN N)) := by
  rw [← Real.rpow_intCast (2 : ℝ) ((d : ℤ) * ((k : ℤ) - Work.Analysis.EndVar.logN N))]
  push_cast
  ring

theorem randSymbG_support_le (rho : Real) (P : Polynomial Int) (C0 : Nat) (a : Nat → NNReal)
    (l1 l2 k1 k2 : Nat) (t : Real) (eps : Nat → Complex) (K : Nat) (R : Real)
    (hR : ∀ n : Nat, Work.KMTAreas.A7.smallCond rho C0 a l1 l2 k1 k2 n →
      (2 : Real) ^ ((P.natDegree : Int) * ((k2 : Int) - Work.Analysis.EndVar.logN (Nat.floor (a n)))) ≤ R) :
    ∀ xi : Real, Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbG rho P C0 a l1 l2 k1 k2 t) eps K xi ≠ 0 →
      |xi| ≤ R := by
  intro ξ hξ
  -- rewrite the symbol as a sum of the (explicitly described) bumps
  set ψ : ℕ → ℂ := fun m =>
    if randAct rho C0 a l1 l2 k1 k2 m then
      varphitildeNt P P.natDegree (Nat.floor (a m)) k2 t ξ else 0 with hψ
  have hφξ : ∀ m : ℕ, smallSymbG rho P C0 a l1 l2 k1 k2 t m ξ = ψ m := by
    intro m
    rw [congrFun (smallSymbG_apply rho P C0 a l1 l2 k1 k2 t m) ξ]
    by_cases hc : randAct rho C0 a l1 l2 k1 k2 m <;> simp [hψ, hc]
  have hsum : randSymb (smallSymbG rho P C0 a l1 l2 k1 k2 t) eps K ξ
      = ∑ n ∈ Finset.range K, eps n * (ψ (n + 1) - ψ n) := by
    simp only [randSymb, hφξ]
  rw [hsum] at hξ
  -- a nonzero sum has a nonzero summand
  obtain ⟨n, -, hnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hξ
  have hdiff : ψ (n + 1) ≠ 0 ∨ ψ n ≠ 0 := by
    by_contra h
    push Not at h
    exact hnz (by rw [h.1, h.2, sub_zero, mul_zero])
  -- a nonzero bump value carries both `smallCond` and the support bound
  have key : ∀ r : ℕ, ψ r ≠ 0 → smallCond rho C0 a l1 l2 k1 k2 r ∧
      varphitildeNt P P.natDegree (Nat.floor (a r)) k2 t ξ ≠ 0 := by
    intro r hr
    have hra : randAct rho C0 a l1 l2 k1 k2 r := by
      by_contra hc; simp [hψ, hc] at hr
    exact ⟨hra.2, by simpa [hψ, hra] using hr⟩
  rcases hdiff with h | h
  · obtain ⟨hsC, hb⟩ := key (n + 1) h
    refine le_trans (varphitildeNt_support_all P P.natDegree (Nat.floor (a (n + 1))) k2 t ξ hb) ?_
    rw [rpow_natDegree_sub_logN]
    exact hR (n + 1) hsC
  · obtain ⟨hsC, hb⟩ := key n h
    refine le_trans (varphitildeNt_support_all P P.natDegree (Nat.floor (a n)) k2 t ξ hb) ?_
    rw [rpow_natDegree_sub_logN]
    exact hR n hsC

end

end Work.KMTAreas.A7
