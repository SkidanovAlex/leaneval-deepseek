/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.AFormulaDegree

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial
open scoped BigOperators

/-!
# The Frobenius identity for Carlitz's power-sum polynomials

The level-one power-sum polynomials `A_n = ∑_{c∈F} Q_c^n = [1]^n P_1(n)` satisfy the Frobenius
identity
```
A_(n q) = (A_n)^q          (q = Nat.card F)
```
because `(∑_c Q_c^n)^q = ∑_c Q_c^(nq)` (Freshman's dream in characteristic `p`).  Combined with the
closed form for the degree (`AFormulaDegree.natDegree_A`) this gives the scaling of the maximizing
index `m*`:
```
m* (n q) = q · m* (n)      (1 ≤ n),
```
and hence the known scaling `T(qz) = q·T(z)` for Thakur's map `T z = z + jMin z`
(`jMin_mulCard`; `PrimeDominates.TT_mul_p` proves the prime-`q` case in a different normalisation).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ `A_(n q) = (A_n)^q`: the Frobenius identity for the power-sum polynomials. -/
theorem A_mul_card (n : ℕ) : A F (n * Nat.card F) = (A F n) ^ Nat.card F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hL : (∑ c : F, (qPoly F c) ^ (n * Nat.card F)) =
      ∑ c : F, ((qPoly F c) ^ n) ^ Nat.card F :=
    Finset.sum_congr rfl fun c _ => pow_mul _ _ _
  show (∑ c : F, (qPoly F c) ^ (n * Nat.card F)) = (∑ c : F, (qPoly F c) ^ n) ^ Nat.card F
  rw [hL, ← carlitz_sum_pow_card F Finset.univ (fun c : F => (qPoly F c) ^ n)]

/-- ★★ The scaling of the maximizing index: `m* (n q) = q · m* n` for `1 ≤ n`. -/
theorem mStar_mul_card (n : ℕ) (hn : 1 ≤ n) :
    mStar F (n * Nat.card F) = Nat.card F * mStar F n := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have hnq : 1 ≤ n * Nat.card F :=
    Nat.mul_pos (by omega : 0 < n) (by omega : 0 < Nat.card F)
  have key : (Nat.card F - 1) * Nat.card F * mStar F (n * Nat.card F) =
      (Nat.card F - 1) * Nat.card F * (Nat.card F * mStar F n) := by
    rw [← natDegree_A F (n * Nat.card F) hnq, A_mul_card F n, Polynomial.natDegree_pow,
      natDegree_A F n hn]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega)) key

/-- The argument `q · n` (`q = Nat.card F`) in `ℕ+`. -/
noncomputable def mulCard (n : ℕ+) : ℕ+ :=
  ⟨(n : ℕ) * Nat.card F, Nat.mul_pos n.pos (by have := card_ge_two F; omega)⟩

lemma mulCard_coe (n : ℕ+) : ((mulCard F n : ℕ+) : ℕ) = (n : ℕ) * Nat.card F := rfl

/-- ★★ The scaling of Thakur's least admissible shift: `jMin (q n) = q · jMin n`. -/
theorem jMin_mulCard (n : ℕ+) : jMin F (mulCard F n) = Nat.card F * jMin F n := by
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  rw [jMin_eq_mStar F (mulCard F n), jMin_eq_mStar F n,
    show ((mulCard F n : ℕ+) : ℕ) = (n : ℕ) * Nat.card F from rfl,
    mStar_mul_card F (n : ℕ) n.pos]
  have hle : Nat.card F * mStar F (n : ℕ) ≤ (n : ℕ) := card_mul_mStar_le F (n : ℕ)
  have hle2 : Nat.card F * (Nat.card F * mStar F (n : ℕ)) ≤ (n : ℕ) * Nat.card F :=
    calc Nat.card F * (Nat.card F * mStar F (n : ℕ)) ≤ Nat.card F * (n : ℕ) :=
          Nat.mul_le_mul_left _ hle
      _ = (n : ℕ) * Nat.card F := Nat.mul_comm _ _
  refine Nat.cast_injective (R := ℤ) ?_
  push_cast [Nat.cast_sub hle2, Nat.cast_sub hle]
  ring

end ZagierHoffmanPositiveChar

namespace AFrobeniusRegression

attribute [local instance 100] Classical.decEq

open ZagierHoffmanPositiveChar

/-- `A_4 = (A_2)^2` over `F₂`. -/
example : A (ZMod 2) (2 * Nat.card (ZMod 2)) = (A (ZMod 2) 2) ^ Nat.card (ZMod 2) :=
  A_mul_card (ZMod 2) 2

/-- `m* (2·3) = 3·m* (2)` over `F₃`. -/
example : mStar (ZMod 3) (2 * Nat.card (ZMod 3)) = Nat.card (ZMod 3) * mStar (ZMod 3) 2 :=
  mStar_mul_card (ZMod 3) 2 (by norm_num)

/-- `jMin (2·3) = 3·jMin 2` over `F₃`. -/
example : jMin (ZMod 3) (mulCard (ZMod 3) 2) =
    Nat.card (ZMod 3) * jMin (ZMod 3) 2 :=
  jMin_mulCard (ZMod 3) 2

end AFrobeniusRegression
