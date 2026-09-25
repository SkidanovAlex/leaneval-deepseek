/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tameness *characterised* by the affinity of the Herbrand function

For a finite Galois extension `L/K` of local fields with valuation ring `A ⊆ L`, the lower
numbering of the ramification filtration is `G_i` (`NK.Ramification.ramificationSubgroup`),
`g_i = #G_i = lowerIndex A i`, and the Herbrand function is

  `φ(n) = (g_0 + g_1 + ⋯ + g_{n-1}) / g_0`   (`NK.Ramification.herbrand`).

In `NK.Ramification.herbrand_of_tame` it is proved that a *tamely* ramified extension — that is,
one with trivial wild inertia `G_1` (`IsTamelyRamified A`) — has the affine Herbrand function

  `φ(n) = 1 + (n - 1)/g_0`   for all `n ≥ 1`,

the lower indices being `g_0 = #I` and `g_i = 1` for `i ≥ 1`.

Here the **converse** is proved: the affinity of `φ` on the *integers* forces tameness.  Indeed
the value at `n = 2` reads `(g_0 + g_1)/g_0 = 1 + 1/g_0`, whence `g_1 = g_0 · (1/g_0) = 1`, and
a subgroup of order `1` is trivial (`lowerIndex_eq_one_iff`).  Note that `n = 1` gives no
information (`φ(1) = 1` in every finite extension), so the single condition at `n = 2` is the
whole content of the characterisation.  Consequently *`L/K` is tamely ramified if and only if its
Herbrand function is the affine function* `n ↦ 1 + (n-1)/g_0` — the numerical form in which the
tame case enters the reconstruction of a local field from its Galois group
(Neukirch's *Kennzeichnung*: the group `G_K` carries the ramification filtration of `G_K^ab`).
-/
import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
import Submission.NK.Ramification.Determined
import Submission.NK.Ramification.herbrand_of_tame
import Submission.NK.Ramification.lowerIndex_eq_one_iff

namespace NK.Ramification

/-- **Tameness is equivalent to the affinity of the Herbrand function.**

For `A : ValuationSubring L` with finite decomposition subgroup, `L/K` is tamely ramified with
respect to `A` if and only if for every `n ≥ 1`

  `φ(n) = 1 + (n - 1)/g_0`,   `g_0 = lowerIndex A 0`.

The forward implication is `herbrand_of_tame`; the converse is the case `n = 2`, which gives
`g_1 = 1`, i.e. `G_1 = ⊥`. -/
theorem tame_iff_herbrand_linear {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] :
    NK.Ramification.IsTamelyRamified (K := K) A ↔
      ∀ n : ℕ, 1 ≤ n → NK.Ramification.herbrand (K := K) A n =
        1 + ((n : ℚ) - 1) / (NK.Ramification.lowerIndex (K := K) A 0 : ℚ) := by
  constructor
  · -- tamely ramified ⟹ affine `φ`
    intro h n hn
    exact herbrand_of_tame A h n hn
  · -- affine `φ` ⟹ tamely ramified: evaluate at `n = 2` to get `g_1 = 1`
    intro h
    have h2 := h 2 (by norm_num)
    have hg0 : (lowerIndex (K := K) A 0 : ℚ) ≠ 0 := by
      exact_mod_cast (lowerIndex_zero_pos (K := K) A).ne'
    have hmul := herbrand_mul_lowerIndex_zero (K := K) A 2
    rw [h2] at hmul
    norm_num at hmul
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hmul
    rw [mul_add, mul_one, mul_inv_cancel₀ hg0] at hmul
    have hg1q : (lowerIndex (K := K) A 1 : ℚ) = 1 := by linarith
    have hg1 : lowerIndex (K := K) A 1 = 1 := by exact_mod_cast hg1q
    exact (lowerIndex_eq_one_iff A 1).mp hg1

end NK.Ramification
