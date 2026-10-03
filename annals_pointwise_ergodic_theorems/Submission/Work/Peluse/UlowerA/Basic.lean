import Mathlib
import Submission.Work.Peluse.Ulower.ss_char_entry_defs

/-!
# The `A`-scale bookkeeping for the degree-lowering chapter

The degree-lowering statement `Work.Peluse.Ulower.degree_lowering_A` replaces the balanced scale
relation `Scaled Ns N d` (`N^d/2 ≤ Ns ≤ 2 N^d`) of `Work.Peluse.Ulower.degree_lowering_v2` by the
*unbalanced* two-sided relation `N^d ≤ A·Ns`, `Ns ≤ A·N^d` with a fixed natural number `A ≥ 1`.

Every use of `Scaled` in the degree-lowering chain (`Ulower/assemble.lean`,
`Ulower/chain.lean`, `Ulower/finalTarget.lean`, `Ulower/StepLe/levelTwoExtract.lean`) goes through
the single numerical bound `Work.Peluse.Ulower.dSup_div_add_one_le`:
`Scaled Ns N d` implies `dSup P Ns N + 1 ≤ ssAmax P · Ns`.

The point of this module is that the unbalanced relation implies the *same kind* of bound, with the
constant `ssAmax P` replaced by `2 + coeffSum P · A`: the support box `dSup P Ns N = Ns + polySup P N`
grows at most linearly in `Ns` because `polySup P N ≤ coeffSum P · N^d ≤ coeffSum P · A · Ns`.

This is the single numerical input that all the `A`-versions of the chain pieces consume.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.UlowerA

open Polynomial

/-- `polySup P N ≤ coeffSum P · N ^ deg P` for `N ≥ 1`. -/
lemma polySup_le_coeffSum_mul_pow (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) :
    Work.Peluse.polySup P N ≤ Work.Peluse.Ulower.coeffSum P * N ^ P.natDegree := by
  rw [Work.Peluse.polySup, Work.Peluse.Ulower.coeffSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN hi')

/-- **The unbalanced scale relation gives the support-box bound.**

If `N ^ deg P ≤ A · Ns` with `A ≥ 1`, `N ≥ 1`, `Ns ≥ 1`, then
`dSup P Ns N + 1 ≤ (2 + coeffSum P * A) * Ns`. -/
theorem dSup_add_one_le_of_unbal {P : Polynomial ℤ} {A Ns N : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N)
    (hNs : 1 ≤ Ns) (hd : (N : ℝ) ^ P.natDegree ≤ (A : ℝ) * (Ns : ℝ)) :
    Work.Peluse.dSup P Ns N + 1 ≤ (2 + Work.Peluse.Ulower.coeffSum P * A) * Ns := by
  -- `N ^ deg P ≤ A * Ns` in `ℕ`
  have hpow : N ^ P.natDegree ≤ A * Ns := by
    have h2 : ((N ^ P.natDegree : ℕ) : ℝ) ≤ ((A * Ns : ℕ) : ℝ) := by
      push_cast
      exact hd
    exact_mod_cast h2
  -- `polySup P N ≤ coeffSum P * A * Ns`
  have hpoly : Work.Peluse.polySup P N ≤ Work.Peluse.Ulower.coeffSum P * A * Ns := by
    refine le_trans (polySup_le_coeffSum_mul_pow P hN) ?_
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ hpow
  have hdSup : Work.Peluse.dSup P Ns N ≤ Ns + Work.Peluse.Ulower.coeffSum P * A * Ns := by
    rw [Work.Peluse.dSup]
    exact Nat.add_le_add_left hpoly Ns
  have hkey : Ns + 1 ≤ 2 * Ns := by omega
  calc Work.Peluse.dSup P Ns N + 1
      ≤ Ns + Work.Peluse.Ulower.coeffSum P * A * Ns + 1 := Nat.add_le_add_right hdSup 1
    _ = (Ns + 1) + Work.Peluse.Ulower.coeffSum P * A * Ns := by ring
    _ ≤ 2 * Ns + Work.Peluse.Ulower.coeffSum P * A * Ns := Nat.add_le_add_right hkey _
    _ = (2 + Work.Peluse.Ulower.coeffSum P * A) * Ns := by ring

end Work.Peluse.UlowerA
