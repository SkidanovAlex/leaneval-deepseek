import Submission.ZagierHoffmanProof.StepK9

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K13: assembly of the R1 chain — `R1(d) ∀d` from ID2

`R1Prop(d)` is paper (2.8): `P_d(q) + D1·S_{d+1}(1, q−1) = 0`.  The chain so far:
base `R1_zero` (StepK6), induction step `R1_step` (StepK8, needs `P F (n+1) 1 ≠ 0`
and `ID2(n+1)`), Frobenius `P_e(q) = (P_e(1))^q` (StepK9).  This file assembles the
outer mutual induction:

    R1_induction : (∀ n ≥ 1, ID2 F n) → R1Prop(d) ∧ P F d oneExp ≠ 0

using `R1Prop(d)` itself to bootstrap the next-level nonvanishing
(`P F d q = 0 ⇒ (P F d 1)^q = 0 ⇒ P F d 1 = 0`, char-p power), and hence

    R1_all        : (∀ n ≥ 1, ID2 F n) → ∀ d, R1Prop F d
    P_oneExp_ne_zero_all : (∀ n ≥ 1, ID2 F n) → ∀ d, P F d oneExp ≠ 0

The single remaining open mathematical input is `ID2` (equivalently the power-sum
evaluation `U_d = 1/ℓ_d`, PLAN Sessions 109–118); everything else in the R1 chain is
now closed.  All lemmas here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Mutual induction: `R1Prop(d)` and the exponent-1 power-sum nonvanishing
`P F d oneExp ≠ 0`, assuming ID2 at every level ≥ 1. -/
lemma R1_induction (hid2 : ∀ n : ℕ, 1 ≤ n → ID2 F n) (d : ℕ) :
    R1Prop F d ∧ P F d oneExp ≠ 0 := by
  classical
  let K := RatFunc.CompletionAtInfty F
  induction d with
  | zero =>
      constructor
      · simpa [R1Prop, qExp, qMinusExp, oneExp, D1c] using (R1_zero F)
      · have h1 : (1 : K) ≠ 0 := by exact one_ne_zero
        rw [P_zero_eq_one F oneExp]
        exact h1
  | succ d ih =>
      -- nonvanishing at d+1 from R1Prop(d) + P F d 1 ≠ 0:
      -- P F (d+1) 1 = 0 forces P F d q = 0 (via R1Prop(d)) and hence P F d 1 = 0 (Frobenius)
      have hb : P F (d + 1) oneExp ≠ 0 := by
        intro hz
        have hprev : R1Prop F d := ih.1
        have hz0 := (R1Prop_eq F d).mp hprev
        have hz1 : P F d (qExp F) = 0 := by
          simp [hz] at hz0
          exact hz0
        have hfrob := P_d_q_eq_pow_one F d
        have hz2 : (P F d oneExp) ^ Nat.card F = 0 := by
          simpa [hfrob] using hz1
        have hq : Nat.card F ≠ 0 := by
          have hq' : 2 ≤ Nat.card F := card_ge_two F
          omega
        have hpz : P F d oneExp = 0 := (pow_eq_zero_iff hq).mp hz2
        exact ih.2 hpz
      constructor
      · exact R1_step F d hb ih.1 (hid2 (d + 1) (by omega))
      · exact hb

/-- ★ R1 (paper (2.8)) at every level `d`, assuming ID2 at every level `d ≥ 1`:
`P_d(q) + D1·S_{d+1}(1, q−1) = 0` for all `d`. -/
theorem R1_all (hid2 : ∀ n : ℕ, 1 ≤ n → ID2 F n) : ∀ d : ℕ, R1Prop F d := by
  intro d
  exact (R1_induction F hid2 d).1

/-- Exponent-1 power-sum nonvanishing at every level, assuming ID2. -/
theorem P_oneExp_ne_zero_all (hid2 : ∀ n : ℕ, 1 ≤ n → ID2 F n) : ∀ d : ℕ, P F d oneExp ≠ 0 := by
  intro d
  exact (R1_induction F hid2 d).2

end ZagierHoffmanPositiveChar
