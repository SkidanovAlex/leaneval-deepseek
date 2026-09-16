import Submission.ZagierHoffmanProof.StepK7

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K8: R1_step — the induction step of the R1 chain

`R1Prop (d)` is paper (2.8) at level d.  The depth-two block splits
`S F 2 (pair 1 (q−1)) (d+1) = P F (d+1) 1 · Td(d)` (`S_two_expand`), and `Td`
telescopes (`Td_succ`).  The induction step (Session-104-addendum reduction):
`R1Prop(n+1)` follows from `R1Prop(n)`, `ID2(n+1)` and `P_mul_qminus(n+1)`, provided
`P F (n+1) oneExp ≠ 0` (power-sum nonvanishing — bootstrapped in the outer induction,
see PLAN).  All lemmas here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Expansion of the depth-two block: `S F 2 (pair 1 (q−1)) (d+1) = P F (d+1) 1 · Td(d)`. -/
lemma S_two_expand (d : ℕ) :
    S F 2 (by omega : 0 < 2) (pair oneExp (qMinusExp F)) (d + 1) =
      P F (d + 1) oneExp * Td F d := by
  classical
  rw [Td]
  rw [← consVec_single_eq_pair oneExp (qMinusExp F)]
  exact S_cons_rec F (by omega : 0 < 1) oneExp (single (qMinusExp F)) (d + 1)

/-- Telescoping of the level-sum `Td`: `Td(d+1) = Td(d) + P F (d+1) (q−1)`. -/
lemma Td_succ (d : ℕ) :
    Td F (d + 1) = Td F d + P F (d + 1) (qMinusExp F) := by
  classical
  dsimp [Td]
  rw [S_lt_succ F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1)]
  congr 1
  rw [S_one_eq_P F (d + 1) (by omega : 0 < 1) (single (qMinusExp F))]
  change P F (d + 1) (qMinusExp F) = P F (d + 1) (qMinusExp F)
  rfl

/-- `R1Prop(d)` equals its `Td`-expanded form. -/
lemma R1Prop_eq (d : ℕ) :
    R1Prop F d ↔ P F d (qExp F) + D1c F * (P F (d + 1) oneExp * Td F d) = 0 := by
  classical
  change (P F d (qExp F) + D1c F * S F 2 (by omega : 0 < 2) (pair oneExp (qMinusExp F)) (d + 1) = 0)
      ↔ P F d (qExp F) + D1c F * (P F (d + 1) oneExp * Td F d) = 0
  rw [S_two_expand F d]

/-- ★ The R1 induction step: `R1Prop(n+1)` from `R1Prop(n)` + `ID2(n+1)` +
`P_mul_qminus(n+1)`, assuming the power sum `P F (n+1) oneExp` is nonzero. -/
theorem R1_step (n : ℕ) (hb : P F (n + 1) oneExp ≠ 0)
    (hprev : R1Prop F n) (hid : ID2 F (n + 1)) : R1Prop F (n + 1) := by
  classical
  let A : RatFunc.CompletionAtInfty F := P F (n + 1) (qExp F)
  let B : RatFunc.CompletionAtInfty F := P F (n + 1) oneExp
  let C : RatFunc.CompletionAtInfty F := P F (n + 2) oneExp
  let E : RatFunc.CompletionAtInfty F := P F n (qExp F)
  let M : RatFunc.CompletionAtInfty F := P F (n + 1) (qMinusExp F)
  let U : RatFunc.CompletionAtInfty F := Td F n
  let D : RatFunc.CompletionAtInfty F := D1c F
  have hp : B * M = A := by
    dsimp [B, M, A]
    exact P_mul_qminus F (n + 1)
  have hprevE : E + D * (B * U) = 0 := by
    have hx := (R1Prop_eq F n).mp hprev
    simpa [A, B, C, E, M, U, D] using hx
  have hidE : A * (B + D * C) = C * E := by
    simpa [ID2, A, B, C, E, M, U, D] using hid
  have hm : B * (A + D * (C * (U + M))) = 0 := by
    calc
      B * (A + D * (C * (U + M)))
          = B * A + B * (D * C * U) + B * (D * C * M) := by ring
      _ = B * A + D * C * (B * U) + D * C * (B * M) := by ring
      _ = B * A + D * C * (B * U) + D * C * A := by
            rw [hp]
      _ = A * (B + D * C) + D * C * (B * U) := by ring
      _ = C * E + D * C * (B * U) := by
            rw [hidE]
      _ = C * (E + D * (B * U)) := by ring
      _ = C * 0 := by
            rw [hprevE]
      _ = 0 := by simp
  have htar : A + D * (C * (U + M)) = 0 := by
    exact (mul_eq_zero.mp hm).resolve_left hb
  have ht : Td F (n + 1) = U + M := by
    rw [Td_succ F n]
  exact (R1Prop_eq F (n + 1)).mpr (by
    rw [ht]
    simpa [A, B, C, E, M, U, D] using htar)

end ZagierHoffmanPositiveChar
