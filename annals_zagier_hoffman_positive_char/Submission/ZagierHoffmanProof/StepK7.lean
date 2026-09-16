import Submission.ZagierHoffmanProof.StepK6

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K7: the R1/ID2 frontier — formal statements (paper (2.8) and the 3-term recurrence)

R1 (paper (2.8)): `S_d(q) + D1·S_{d+1}(1, q−1) = 0` for every level d.  The level-0 case
`R1_zero` is proven (StepK6).  The Session-104-addendum reduction shows
`R1(d) ⇐ R1(d−1) ∧ ID2(d) ∧ P_mul_qminus(d)` with

  ID2(d) : `P_d(q)·(P_d(1) + D1·P_{d+1}(1)) = P_{d+1}(1)·P_{d−1}(q)`   (d ≥ 1)

(numerically verified for q ∈ {2,3,5}; equivalent to the clean first-order recurrence
`w_d = w_{d−1}^{−q} − D1` for `w_d := P_d(1)/P_{d+1}(1)`).  This file records the exact
formal statements (all sorry-free definitions) so the frontier is concrete in Lean; the
proofs of ID2 (and hence of `R1(d)` for all d) are the next milestone.
-/
namespace ZagierHoffmanPositiveChar
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `D1 := X^q − X` as an element of the completion `K∞`. -/
noncomputable def D1c : RatFunc.CompletionAtInfty F :=
  (((carlitzOne F : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)

/-- the exponent `q = |F|`. -/
noncomputable def qExp : ℕ+ :=
  ⟨Nat.card F, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩

/-- the exponent `q − 1`. -/
noncomputable def qMinusExp : ℕ+ :=
  ⟨Nat.card F - 1, by have hq : 2 ≤ Nat.card F := card_ge_two F; omega⟩

/-- the exponent `1`. -/
noncomputable def oneExp : ℕ+ := ⟨1, by omega⟩

/-- ★ ID2 (3-term recurrence, numerically verified q ∈ {2,3,5}): for every level d ≥ 1,
`P_d(q)·(P_d(1) + D1·P_{d+1}(1)) = P_{d+1}(1)·P_{d−1}(q)` in `K∞`. -/
def ID2 (d : ℕ) : Prop :=
  P F d (qExp F) * (P F d oneExp + D1c F * P F (d + 1) oneExp) =
    P F (d + 1) oneExp * P F (d - 1) (qExp F)

/-- R1 (paper (2.8)) at level `d`: `S_d(q) + D1·S_{d+1}(1, q−1) = 0`. -/
def R1Prop (d : ℕ) : Prop :=
  P F d (qExp F) + D1c F * S F 2 (by omega : 0 < 2) (pair oneExp (qMinusExp F)) (d + 1) = 0

/-- `T_d = S_<d+1(q−1) = Σ_{e ≤ d} P_e(q−1)`: the telescoping sum in the R1 reduction. -/
noncomputable def Td (d : ℕ) : RatFunc.CompletionAtInfty F :=
  S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1)

end ZagierHoffmanPositiveChar
