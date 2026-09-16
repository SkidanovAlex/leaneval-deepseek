/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.ATBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial
open scoped BigOperators

/-!
# Regression checks for the Anderson–Thakur ↔ power-sum bridge (`ATBridge`)

The bridge `psi_CPoly'` was validated numerically (exact `F_q[θ]` arithmetic, `q ∈ {2,3,4,5,9}`,
`n ≤ 6`, specialising the recursion for `c_n` at `t ↦ θ^q` and comparing with `(-1)^(n+1)A_(n+1)`;
script `/tmp/ses299/br.py`).  This file records the formal consequences that pin the statement down:
the clearing sequence at `n = 1` is `Λ_1 = D_1^2`, the Anderson–Thakur coefficient `c_1 = 1` so that
`CPoly 1 = Λ_1`, and the bridge then forces `b_1 = A_2 = 1`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `Λ_1 = D_1 ^ 2`. -/
lemma LamPoly_one : LamPoly F 1 = (atDpoly F 1) ^ 2 := by
  rw [LamPoly, Finset.prod_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.prod_empty]
  norm_num

/-- `M(1,0) = D_1 ^ 2`. -/
lemma Mpoly_one : Mpoly F 1 0 = (atDpoly F 1) ^ 2 := by
  rw [Mpoly, Finset.prod_range_succ, Finset.prod_range_succ, Finset.range_zero,
    Finset.prod_empty]
  norm_num [atDpoly_zero]

/-- The Anderson–Thakur coefficient `c_1 = 1` (`1 < q`), so `CPoly 1 = M(1,0) = Λ_1`. -/
lemma CPoly_one : CPoly F 1 = LamPoly F 1 := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  rw [CPoly_succ F (by norm_num : (1 : ℕ) ≠ 0),
    show (Finset.range (1 + 1)).filter (fun j => Nat.card F ^ j ≤ 1) = {0} from by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hjq⟩
        by_contra h0
        have h1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr h0
        have hle : Nat.card F ≤ Nat.card F ^ j := by
          conv_lhs => rw [← pow_one (Nat.card F)]
          exact Nat.pow_le_pow_right (by omega) h1
        omega
      · rintro rfl
        exact ⟨by omega, by rw [pow_zero]⟩,
    Finset.sum_singleton, show 1 - Nat.card F ^ 0 = 0 by rw [pow_zero, Nat.sub_self], CPoly_zero,
    atGammaPoly, Finset.Icc_eq_empty (by omega), Finset.prod_empty, one_mul, mul_one,
    Mpoly_one F, LamPoly_one F]

/-- Consistency: with `CPoly 1 = Λ_1` the bridge at `n = 1` collapses to `b_1 = 1`, i.e. `A_2 = 1`
(which is Carlitz's easy range `A_n = (-1)^n` for `n ≤ q`). -/
lemma bridge_check_one : bspec F 1 = 1 := by
  have h := psi_CPoly' F 1
  rw [CPoly_one F] at h
  have hne : psi F (LamPoly F 1) ≠ 0 := psi_LamPoly_ne_zero F 1
  have h2 : (1 : F[X]) * psi F (LamPoly F 1) = bspec F 1 * psi F (LamPoly F 1) := by
    rw [one_mul]
    exact h
  exact (mul_right_cancel₀ hne h2).symm

/-- `bspec 1 = A_2`. -/
lemma bspec_one : bspec F 1 = A F 2 := by
  rw [bspec]
  norm_num

end ZagierHoffmanPositiveChar

namespace ATBridgeRegression

attribute [local instance 100] Classical.decEq

open ZagierHoffmanPositiveChar

/-- The bridge over `F₂` at `n = 2`. -/
example : psi (ZMod 2) (CPoly (ZMod 2) 2) =
    bspec (ZMod 2) 2 * psi (ZMod 2) (LamPoly (ZMod 2) 2) :=
  psi_CPoly' (ZMod 2) 2

/-- The bridge over `F₃` at `n = 3`. -/
example : psi (ZMod 3) (CPoly (ZMod 3) 3) =
    bspec (ZMod 3) 3 * psi (ZMod 3) (LamPoly (ZMod 3) 3) :=
  psi_CPoly' (ZMod 3) 3

/-- The bridge over the non-prime field `F₄`. -/
example : psi (GaloisField 2 2) (CPoly (GaloisField 2 2) 4) =
    bspec (GaloisField 2 2) 4 * psi (GaloisField 2 2) (LamPoly (GaloisField 2 2) 4) :=
  psi_CPoly' (GaloisField 2 2) 4

example : LamPoly (ZMod 3) 1 = (atDpoly (ZMod 3) 1) ^ 2 := LamPoly_one (ZMod 3)

example : CPoly (ZMod 3) 1 = LamPoly (ZMod 3) 1 := CPoly_one (ZMod 3)

example : bspec (ZMod 3) 1 = 1 := bridge_check_one (ZMod 3)

/-- The cleared coefficient of `n = 1` in `F(θ,t)`: `Λ_1 · c_1 = Λ_1`. -/
example : (algebraMap ((ZMod 2)[X])[X] (atQ (ZMod 2)) (LamPoly (ZMod 2) 1) : atQ (ZMod 2)) *
    atCoeff (ZMod 2) 1 = algebraMap ((ZMod 2)[X])[X] (atQ (ZMod 2)) (CPoly (ZMod 2) 1) :=
  LamPoly_mul_atCoeff (ZMod 2) 1

end ATBridgeRegression
