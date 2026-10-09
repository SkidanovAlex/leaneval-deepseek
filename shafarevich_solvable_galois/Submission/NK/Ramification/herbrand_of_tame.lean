/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Herbrand function of a tamely ramified extension

For a finite Galois extension `L/K` of local fields with valuation ring `A ⊆ L`, the Herbrand
function `φ` (`NK.Ramification.herbrand`) is

  `φ(n) = (g_0 + g_1 + ⋯ + g_{n-1}) / g_0`,   `g_i = #G_i = lowerIndex A i`.

If `L/K` is at most **tamely ramified** — `IsTamelyRamified A`, i.e. the wild inertia `G_1` is
trivial — then the ramification filtration is trivial from level `1` on
(`ramificationSubgroup_eq_bot_of_tame`), so `g_i = 1` for every `i ≥ 1`
(`lowerIndex_eq_one_of_tame`), `g_0 = #I` is the inertia degree, and `φ` is the affine function

  `φ(n) = 1 + (n - 1)/g_0`   (`n ≥ 1`),

the classical formula `∫_0^n dt/[G_0:G_t]` with `[G_0:G_t] = g_0` on `[0,1)` and `= 1` on
`[1,∞)`.  This file records that identity.
-/
import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
import Submission.NK.Ramification.Determined
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **The Herbrand function of a tamely ramified extension is affine.**

If `L/K` is tamely ramified with respect to the valuation ring `A` (so that the wild inertia
`G_1` is trivial) and the decomposition subgroup `A.decompositionSubgroup K` is finite, then for
every `n ≥ 1`

  `φ(n) = 1 + (n - 1)/g_0`,   `g_0 = #G_0 = lowerIndex A 0`,

the lower indices being `g_0 = #I` and `g_i = 1` for `i ≥ 1`. -/
theorem herbrand_of_tame {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)]
    (h : NK.Ramification.IsTamelyRamified (K := K) A) (n : ℕ) (hn : 1 ≤ n) :
    NK.Ramification.herbrand (K := K) A n =
      1 + ((n : ℚ) - 1) / (NK.Ramification.lowerIndex (K := K) A 0 : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hgpos : 0 < NK.Ramification.lowerIndex (K := K) A 0 :=
    NK.Ramification.lowerIndex_zero_pos (K := K) A
  have hgne : (NK.Ramification.lowerIndex (K := K) A 0 : ℚ) ≠ 0 := by
    exact_mod_cast hgpos.ne'
  have h1 : ∀ i, 1 ≤ i → NK.Ramification.lowerIndex (K := K) A i = 1 :=
    fun i hi => NK.Ramification.lowerIndex_eq_one_of_tame A h hi
  -- the lower indices vanish from level `1` on, so the sum is `g_0 + (n - 1)`
  have hsum :
      (∑ i ∈ Finset.range (k + 1), (NK.Ramification.lowerIndex (K := K) A i : ℚ)) =
        (NK.Ramification.lowerIndex (K := K) A 0 : ℚ) + (k : ℚ) := by
    rw [Finset.sum_range_succ']
    have hk : (∑ i ∈ Finset.range k,
        (NK.Ramification.lowerIndex (K := K) A (i + 1) : ℚ)) = (k : ℚ) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [h1 (i + 1) (by omega)])]
      simp
    rw [hk, add_comm]
  rw [NK.Ramification.herbrand, hsum]
  have hcast : (((k + 1 : ℕ) : ℚ) - 1) = (k : ℚ) := by push_cast; ring
  rw [hcast, add_div, div_self hgne]

end NK.Ramification
