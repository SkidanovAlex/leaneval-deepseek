import Submission.ZagierHoffmanProof.StepB7
import Submission.ZagierHoffmanProof.StepK3

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step K4: first verified R1 ingredients (paper (2.8), level-wise)

The fundamental relation R1 (paper (2.8)) is
`S_d(q) + D1·S_{d+1}(1, q−1) = 0` for every level d ≥ 0, with q = |F| and
D1 = X^q − X (StepA's carlitzOne).  Through `S_d_recursion`,
`S_{d+1}(1,q−1) = P_{d+1}(1)·S_<d+1(q−1)`, so the depth-one evaluations are the core.

This file records the first VERIFIED piece:
★ `P_mul_qminus`: for every level d ≥ 0, `P_d(1)·P_d(q−1) = P_d(q)` —
  the pure product from paper (2.1) with exponents (1, q−1), where every Chen
  coefficient Δ^i_{1,q−1} (i = 1..q−1) vanishes in F (only i = q−1 survives the
  divisibility test, and Δ^{q−1}_{1,q−1} = 1 + (−1)^{q−2} ∈ {0, 2} = 0 in char p).
  (d = 0 case: P_zero_eq_one; d ≥ 1 case: P_pure (StepB4).)
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- q = |F| ≥ 2 as a reusable local fact. -/
lemma card_ge_two (F : Type*) [Field F] [Finite F] : 2 ≤ Nat.card F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [← Fintype.card_eq_nat_card]
  exact Fintype.one_lt_card

/-- ★ `P_d(1)·P_d(q−1) = P_d(q)` at every level d (paper (2.1), pure (1,q−1) case). -/
lemma P_mul_qminus (d : ℕ) :
    P F d ⟨1, by omega⟩ * P F d ⟨Nat.card F - 1, by
      have hq : 2 ≤ Nat.card F := card_ge_two F
      omega⟩ = P F d ⟨Nat.card F, by
      have hq : 2 ≤ Nat.card F := card_ge_two F
      omega⟩ := by
  classical
  let a : ℕ+ := ⟨1, by omega⟩
  let b : ℕ+ := ⟨Nat.card F - 1, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩
  let c : ℕ+ := ⟨Nat.card F, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩
  have ha : (a : ℕ) = 1 := rfl
  have hb : (b : ℕ) = Nat.card F - 1 := rfl
  have hc : (c : ℕ) = Nat.card F := rfl
  change P F d a * P F d b = P F d c
  by_cases hd : 1 ≤ d
  · have hpp := P_pure F d hd a b (by
        rw [ha, hb]
        have hq : 2 ≤ Nat.card F := card_ge_two F
        omega)
    rw [hpp]
    have hX : (⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ : ℕ+) = c := by
      apply Subtype.ext
      change (a : ℕ) + (b : ℕ) = (c : ℕ)
      rw [ha, hb, hc]
      have hq : 1 ≤ Nat.card F := by
        have hq2 : 2 ≤ Nat.card F := card_ge_two F
        omega
      omega
    rw [hX]
  · have hd0 : d = 0 := by omega
    subst d
    change P F 0 a * P F 0 b = P F 0 c
    rw [P_zero_eq_one F a]
    rw [P_zero_eq_one F b]
    rw [P_zero_eq_one F c]
    simp

end ZagierHoffmanPositiveChar
