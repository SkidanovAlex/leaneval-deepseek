/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.ATBridge
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_X

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial
open scoped BigOperators

/-!
# The generating function of the specialisation sequence

The sequence `b_n = (-1)^(n+1) A_(n+1)` (the specialisation `t ↦ θ^q` of the Anderson–Thakur
coefficients, `ATBridge.bspec`) satisfies `b_n = b_(n-1) - [1]^(q-1) b_(n-q)` (with the degenerate
recursion `b_n = b_(n-1)` for `1 ≤ n < q`).  Consequently its generating function is rational:

  `Σ_{n ≥ 0} b_n z^n = 1 / (1 - z + [1]^(q-1) z^q)`,

equivalently `Σ_n A_n z^n = -z / (1 + z - [1]^(q-1) z^q)` — Carlitz's classical form of the
power-sum expansion (`AExpansion.A_thakur_formula`).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `A_0 = q = 0`: the empty power sum vanishes. -/
lemma A_zero : A F 0 = 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hsum : A F 0 = ∑ _c : F, (1 : F[X]) := by
    rw [show A F 0 = ∑ c : F, (qPoly F c) ^ 0 from rfl]
    exact Finset.sum_congr rfl fun c _ => by rw [pow_zero]
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  obtain ⟨n, hprime, hn⟩ := card_eq_ringChar_pow F
  rw [Nat.card_eq_fintype_card] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have h2 : 2 ≤ Fintype.card F := by rw [← Nat.card_eq_fintype_card]; exact card_ge_two F
    omega
  exact (CharP.cast_eq_zero_iff (F[X]) (ringChar F) (Fintype.card F)).mpr
    (by rw [hn]; exact dvd_pow_self _ hn0)

/-- ★★ The generating function of the specialisation sequence:
`(Σ_n b_n z^n)·(1 - z + [1]^(q-1) z^q) = 1`. -/
theorem bspec_genfun :
    PowerSeries.mk (fun n => bspec F n) *
      (1 - PowerSeries.X + PowerSeries.C ((carlitzOne F) ^ (Nat.card F - 1)) *
        PowerSeries.X ^ Nat.card F) = 1 := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  refine PowerSeries.ext fun n => ?_
  rw [mul_add, mul_sub, mul_one, map_add, map_sub, Commons.RingTheory.PowerSeries.coeff_mul_X,
    ← mul_assoc, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [if_neg (by decide : ¬ (1 : ℕ) ≤ 0), if_neg (Nat.not_le.mpr Nat.card_pos), if_pos rfl,
      bspec_zero]
    ring
  · rw [if_pos (show (1 : ℕ) ≤ n from hnpos), if_neg (by omega : ¬ n = 0)]
    by_cases hnN : Nat.card F ≤ n
    · rw [if_pos hnN, bspec_succ F n hnN]
      ring
    · rw [if_neg hnN, bspec_low F n hnpos (by omega)]
      ring

/-- ★★ The generating function in Carlitz's form:
`(Σ_n A_n z^n)·(1 + z - [1]^(q-1) z^q) = -z`. -/
theorem A_genfun :
    PowerSeries.mk (fun n => A F n) *
      (1 + PowerSeries.X - PowerSeries.C ((carlitzOne F) ^ (Nat.card F - 1)) *
        PowerSeries.X ^ Nat.card F) = -PowerSeries.X := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  refine PowerSeries.ext fun n => ?_
  rw [mul_sub, mul_add, mul_one, map_sub, map_add, Commons.RingTheory.PowerSeries.coeff_mul_X,
    ← mul_assoc, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    map_neg, PowerSeries.coeff_X]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [if_neg (by decide : ¬ (1 : ℕ) ≤ 0), if_neg (Nat.not_le.mpr Nat.card_pos),
      if_neg (by decide : ¬ (0 : ℕ) = 1), A_zero F]
    ring
  · rw [if_pos (show (1 : ℕ) ≤ n from hnpos)]
    by_cases hnN : Nat.card F ≤ n
    · rw [if_neg (by omega : ¬ n = 1), if_pos hnN, A_recursion F n hnN]
      ring
    · rw [if_neg hnN]
      by_cases h1 : n = 1
      · subst h1
        rw [if_pos rfl, A_one_eq_neg_one F, A_zero F]
        ring
      · rw [if_neg h1, A_eq_neg_one_pow F n hnpos (by omega),
          A_eq_neg_one_pow F (n - 1) (by omega) (by omega)]
        rw [show (-1 : F[X]) ^ n = -((-1) ^ (n - 1)) by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [pow_succ]
          ring]
        ring

end ZagierHoffmanPositiveChar
