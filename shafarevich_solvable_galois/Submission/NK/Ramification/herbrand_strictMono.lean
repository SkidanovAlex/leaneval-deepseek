/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict monotonicity of the Herbrand function

The Herbrand function `φ(n) = (g_0 + ⋯ + g_{n-1})/g_0` of `NK.Ramification.Herbrand`
increases by `g_n/g_0` when `n` is replaced by `n+1`.  Since the higher ramification
subgroup `G_n` always contains the identity, `g_n ≥ 1`, and since
`g_0 = #G_0 < ∞` in the finite case, the increment is strictly positive.  Hence `φ` is a
strictly increasing function of the lower index, as required for it to define a change of
numbering of the ramification filtration.
-/
import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **Every lower index is positive** in the finite case: the ramification subgroup `G_i`
always contains the identity, so `g_i = #G_i ≥ 1`.

(The case `i = 0` is `lowerIndex_zero_pos`; the proof is uniform in `i`.) -/
theorem lowerIndex_pos {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] (i : ℕ) :
    0 < lowerIndex (K := K) A i := by
  have : Nonempty ↥(ramificationSubgroup (K := K) A i) :=
    ⟨⟨1, (ramificationSubgroup A i).one_mem⟩⟩
  exact Nat.card_pos

/-- **The recursion of the Herbrand function**: `φ(n+1) = φ(n) + g_n/g_0`.  This is the
discrete form of `φ' = 1/[G_0 : G_t]`. -/
theorem herbrand_succ {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    herbrand (K := K) A (n + 1) =
      herbrand (K := K) A n +
        (lowerIndex (K := K) A n : ℚ) / (lowerIndex (K := K) A 0 : ℚ) := by
  simp only [herbrand, Finset.sum_range_succ, add_div]

/-- **The Herbrand function is strictly increasing at each step**: in the finite case
`φ(n+1) - φ(n) = g_n/g_0 > 0`. -/
theorem herbrand_lt_succ {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] (n : ℕ) :
    herbrand (K := K) A n < herbrand (K := K) A (n + 1) := by
  have hc : (0 : ℚ) < (lowerIndex (K := K) A 0 : ℚ) := by
    exact_mod_cast lowerIndex_zero_pos (K := K) A
  have hgi : (0 : ℚ) < (lowerIndex (K := K) A n : ℚ) := by
    exact_mod_cast lowerIndex_pos (K := K) A n
  rw [herbrand_succ]
  exact lt_add_of_pos_right _ (div_pos hgi hc)

/-- The Herbrand function `φ` is strictly increasing in the lower index, as soon as its
values are finite: each step adds the positive amount `g_n/g_0`. -/
theorem herbrand_strictMono {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] :
    StrictMono (NK.Ramification.herbrand (K := K) A) := by
  exact strictMono_nat_of_lt_succ fun n => herbrand_lt_succ (K := K) A n

end NK.Ramification
