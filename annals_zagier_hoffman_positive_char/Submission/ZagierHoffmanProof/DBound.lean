/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.Counting
import Submission.ZagierHoffmanProof.StepL193

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

/-!
# The bound `d(w) ≤ 2^{w-1}`

The paper's `d(w)` counts the Hoffman tuples: sequences `(s_1, …, s_r)` of positive integers of
weight `w` with `s_i ≤ q` for `i < r` and `s_r < q`.  Every such tuple is a composition of `w`
into positive parts (omit the padding), so `d(w)` is at most the number of compositions of `w`,
which is `2^{w-1}`:

  ★★ `d_le_two_pow (hw : 1 ≤ w) : d F w ≤ 2 ^ (w - 1)`

Combined with Theorem A this bounds the dimension of the weight-`w` space of MZVs:

  ★★ `rank_Z_le_two_pow : Module.rank K (𝒵 w) ≤ 2^{w-1}`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ **The counting bound `d(w) ≤ 2^{w-1}`.** -/
theorem d_le_two_pow (w : ℕ) (hw : 1 ≤ w) : d F w ≤ 2 ^ (w - 1) := by
  classical
  induction w using Nat.strong_induction_on with
  | h w ih =>
    by_cases hlt : w < Nat.card F
    · rw [d_eq_pow_two F hw hlt]
    · by_cases heq : w = Nat.card F
      · subst heq
        rw [d_eq_pow_two_sub_one F]
        exact Nat.sub_le _ _
      · have hg : Nat.card F < w := by omega
        conv_lhs => unfold d
        rw [if_neg (by omega : ¬ w = 0), if_neg (by omega : ¬ w ≤ Nat.card F - 1),
          if_neg (by omega : ¬ w = Nat.card F)]
        have hstep : ∀ i ∈ Finset.range (Nat.card F), d F (w - i - 1) ≤ 2 ^ (w - 2 - i) := by
          intro i hi
          have him : i < Nat.card F := Finset.mem_range.mp hi
          have h1 : 1 ≤ w - i - 1 := by omega
          have h2 : w - i - 1 < w := by omega
          have hthis := ih (w - i - 1) h2 h1
          have he : w - i - 1 - 1 = w - 2 - i := by omega
          rwa [he] at hthis
        calc ∑ i ∈ Finset.range (Nat.card F), d F (w - i - 1)
            ≤ ∑ i ∈ Finset.range (Nat.card F), 2 ^ (w - 2 - i) := Finset.sum_le_sum hstep
          _ ≤ ∑ i ∈ Finset.range (w - 1), 2 ^ (w - 2 - i) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
                (fun i _ _ => Nat.zero_le _)
          _ = 2 ^ (w - 1) - 1 := by
              have h := pow_two_sum_reflect_range (w - 1)
              have he1 : w - 1 - 1 = w - 2 := by omega
              rwa [he1] at h
          _ ≤ 2 ^ (w - 1) := Nat.sub_le _ _

/-- ★★ **The dimension bound `dim_K 𝒵_w ≤ 2^{w-1}`** (Theorem A plus the counting bound). -/
theorem rank_Z_le_two_pow (w : ℕ+) :
    Module.rank (RatFunc F) (𝒵 F (w : ℕ)) ≤ ((2 ^ ((w : ℕ) - 1) : ℕ) : Cardinal) :=
  le_trans (theorem_A_amb F w).2 (Nat.cast_le.mpr (d_le_two_pow F (w : ℕ) w.pos))

/-- ★★ **The recursion for `d`**: for `w ≠ 0, q` the paper's `d` satisfies
`d(w) = Σ_{i=1}^{q} d(w-i)` (this is the defining recursion of `ChallengeDeps.d`). -/
theorem d_rec {w : ℕ} (hw : Nat.card F < w) :
    d F w = ∑ i ∈ Finset.range (Nat.card F), d F (w - (i + 1)) := by
  classical
  conv_lhs => unfold d
  rw [if_neg (by omega : ¬ w = 0), if_neg (by omega : ¬ w ≤ Nat.card F - 1),
    if_neg (by omega : ¬ w = Nat.card F)]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

/-- Sanity: the recursion holds over `F₂` for every `w > 2`. -/
example (w : ℕ) (hw : Nat.card (ZMod 2) < w) :
    d (ZMod 2) w = ∑ i ∈ Finset.range (Nat.card (ZMod 2)), d (ZMod 2) (w - (i + 1)) :=
  d_rec (ZMod 2) hw

end ZagierHoffmanPositiveChar