import Mathlib
import Submission.Work.Peluse.Ulower.ss_char_entry_defs

/-!
# The support-box / scale bookkeeping `dSup P Ns N / |c| + 1 ≤ ssAmax P · Ns`

This is the elementary numerical half of the constant bookkeeping of the `U²`-inverse entry
`Work.Peluse.Ulower.ss_char_entry` (see the docstring of `ss_char_entry_defs`).

Recall

* `dSup P Ns N = Ns + polySup P N` with `polySup P N = ∑_{i ≤ deg P} |a_i| N^i` (`Work.Peluse`),
* `coeffSum P = ∑_{i ≤ deg P} |a_i|` and `ssAmax P = 3 + 2 · coeffSum P` (`Ulower`),
* `Scaled Ns N d` means `N^d / 2 ≤ Ns ≤ 2 N^d`.

The estimate is `Ns + 1 ≤ 3 Ns` (from `Ns ≥ 1`) together with the chain

`dSup P Ns N = Ns + polySup P N ≤ Ns + coeffSum P · N^deg P ≤ Ns + 2 · coeffSum P · Ns`,

the last step being the first half of `Scaled` (`N^deg P ≤ 2 Ns`).  Dividing by `|c| ≥ 1` can only
decrease the left-hand side.

Note that the hypotheses `1 ≤ P.natDegree` and `1 ≤ c.natAbs` are not needed for this inequality
(the bound is valid for every polynomial, and `dSup / 0 = 0`); they are kept because the caller
uses the lemma in that regime.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

/-- For `N ≥ 1` every term `|a_i| N^i` of `polySup P N` (with `i ≤ deg P`) is at most
`|a_i| N ^ deg P`, so `polySup P N ≤ coeffSum P · N ^ deg P`. -/
private lemma polySup_le_coeffSum_mul_pow (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) :
    Work.Peluse.polySup P N ≤ coeffSum P * N ^ P.natDegree := by
  rw [Work.Peluse.polySup, coeffSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN hi')

/-- The first half of `Scaled L M d` (`M ^ d / 2 ≤ L`) implies `M ^ d ≤ 2 L`. -/
private lemma pow_le_two_mul_of_scaled {d L M : ℕ} (h : Work.Peluse.Scaled L M d) :
    M ^ d ≤ 2 * L := by
  have h1 : (M : ℝ) ^ d ≤ 2 * (L : ℝ) := by
    have := h.1
    linarith
  have h2 : ((M ^ d : ℕ) : ℝ) ≤ ((2 * L : ℕ) : ℝ) := by
    push_cast
    exact h1
  exact_mod_cast h2

theorem dSup_div_add_one_le {P : Polynomial ℤ} (hd : 1 ≤ P.natDegree) {c : ℤ}
    (hc1 : 1 ≤ c.natAbs) {Ns N : ℕ} (hNs : 1 ≤ Ns) (hN : 1 ≤ N)
    (hSc : Work.Peluse.Scaled Ns N P.natDegree) :
    (Work.Peluse.dSup P Ns N) / c.natAbs + 1 ≤ Work.Peluse.Ulower.ssAmax P * Ns := by
  -- `polySup P N ≤ coeffSum P · N^deg P ≤ coeffSum P · (2 Ns)`
  have hpoly : Work.Peluse.polySup P N ≤ coeffSum P * (2 * Ns) :=
    le_trans (polySup_le_coeffSum_mul_pow P hN)
      (Nat.mul_le_mul_left _ (pow_le_two_mul_of_scaled hSc))
  -- hence `dSup P Ns N ≤ Ns + coeffSum P · (2 Ns)`
  have hdsup : Work.Peluse.dSup P Ns N ≤ Ns + coeffSum P * (2 * Ns) := by
    rw [Work.Peluse.dSup]
    exact Nat.add_le_add_left hpoly Ns
  -- `Ns ≥ 1` gives `Ns + 1 ≤ 3 Ns`
  have hkey : Ns + 1 ≤ 3 * Ns := by omega
  calc (Work.Peluse.dSup P Ns N) / c.natAbs + 1
      ≤ Work.Peluse.dSup P Ns N + 1 := Nat.add_le_add_right (Nat.div_le_self _ _) 1
    _ ≤ Ns + coeffSum P * (2 * Ns) + 1 := Nat.add_le_add_right hdsup 1
    _ = (Ns + 1) + 2 * coeffSum P * Ns := by ring
    _ ≤ 3 * Ns + 2 * coeffSum P * Ns := Nat.add_le_add_right hkey _
    _ = (3 + 2 * coeffSum P) * Ns := by ring
    _ = Work.Peluse.Ulower.ssAmax P * Ns := by rw [ssAmax]

end Work.Peluse.Ulower
