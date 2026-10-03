/-
# `Work.FIChain.lamPlusBDefs` — the `B`-delay Rosser–Iwaniec weight

The project lead's session-4 construction: the workspace's `lamPlus`/`rdPlus` weight with the
delay exponent `2` replaced by a general real `B` (used with `B = 19`).  Definitions and the two
*free* conjuncts only; the switching recursion (`ρ ≥ 0`) and the Fundamental-Lemma sieve bound are
separate obligations.
-/
import Mathlib

set_option autoImplicit false
namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **`B`-Rosser upper support condition**: every divisor `e` of `d` with an odd number of prime
factors satisfies `e · (minFac e)^B ≤ D`.  (`rdPlus` is the case `B = 2`.) -/
def rdPlusB (B : ℝ) (D : ℝ) (d : ℕ) : Prop :=
  ∀ e ∈ d.divisors, Odd e.primeFactors.card → (e : ℝ) * (e.minFac : ℝ) ^ B ≤ D

/-- The `B`-delay Rosser–Iwaniec upper weight: `μ d` on the `B`-admissible `d`, `0` elsewhere. -/
def lamPlusB (B : ℝ) (D : ℝ) (d : ℕ) : ℝ :=
  if rdPlusB B D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0

lemma lamPlusB_one (B : ℝ) (D : ℝ) (hD : 1 ≤ D) : lamPlusB B D 1 = 1 := by
  rw [lamPlusB]
  have hr : rdPlusB B D 1 := by
    intro e he _
    rw [Nat.divisors_one, Finset.mem_singleton] at he
    subst he
    simpa using hD
  rw [if_pos hr]
  norm_num

lemma lamPlusB_squarefree (B : ℝ) (D : ℝ) : ∀ d : ℕ, ¬ Squarefree d → lamPlusB B D d = 0 := by
  intro d hd
  rw [lamPlusB]
  by_cases h : rdPlusB B D d
  · rw [if_pos h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num
  · rw [if_neg h]

lemma abs_lamPlusB_le_one (B : ℝ) (D : ℝ) : ∀ d : ℕ, |lamPlusB B D d| ≤ 1 := by
  intro d
  rw [lamPlusB]
  by_cases h : rdPlusB B D d
  · rw [if_pos h, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · rw [if_neg h]; norm_num

end
end Work.FIChain
