import Mathlib
import Submission.Work.ConvR.scaleFacts
import Submission.Work.ConvR.scaleInject

/-!
# ConvR/`scaleArrMap`: shared vocabulary

The lemma `Work.ConvR.scaleArrMap` applies a *row* program (whose spec is `RowSpec` below) to every
row of an array `M × r` of fixed-point complex numbers, at cost proportional to `M` times the row
cost.  This file collects the definitions used by the assembler and by the delegated pieces:

* `RowSpec` — the hypothesis on the row program;
* `ArrP` / `ArrErr` / `ArrQ` — the per-element input and output conditions of the `mapList` loop,
  already in the "pre-converted" form consumed by `Work.ConvR.arrExtract`;
* `ArrPre` / `ArrPost` — the whole-array precondition and postcondition;
* `eval_cost_pos` — every `Eval` costs at least one step (used to force `Krow ≥ 1`).
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- The hypothesis on the row program of `Work.ConvR.scaleArrMap`: applied to a coefficient vector
`u ∈ C̃◦^r` (together with `p`, `c` and the rest of the stack) it scales `u` by `c` with the stated
relative error, at cost `Krow * (r+1) * (p+1)^2 + Krow`. -/
def RowSpec (rowProg : Cmd) (Krow : ℕ) : Prop :=
  ∀ (main : Cmd) (p c r : ℕ), 1 ≤ c → c ≤ 2 ^ p →
    ∀ (u : List (ℤ × ℤ)) (rest : List Val), InDiscVec p r u →
      WordR main rowProg
        (fun vs => vs = cvecVal u :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest)
        (fun _ out => ∃ v : List (ℤ × ℤ),
          out = cvecVal v :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest ∧
          InDiscVec p r v ∧
          ∀ (j : Fin r) (x : ℂ), (c : ℝ) * ‖x‖ ≤ 1 →
            (2 : ℝ) ^ p * ‖fxC p (v.getD j (0, 0)) - (c : ℂ) * x‖ <
              2 * c * ((2 : ℝ) ^ p * ‖fxC p (u.getD j (0, 0)) - x‖) + 3)
        (fun _ => Krow * (r + 1) * (p + 1) ^ 2 + Krow)

/-- Per-element input condition of the array map: the value is a row in the disc. -/
def ArrP (p r : ℕ) (x : Val) : Prop :=
  ∃ u : List (ℤ × ℤ), x = cvecVal u ∧ InDiscVec p r u

/-- Per-element output condition: the output row is in the disc and satisfies the row-wise relative
error bound w.r.t. the input row `u`. -/
def ArrErr (p r c : ℕ) (u v : List (ℤ × ℤ)) : Prop :=
  InDiscVec p r v ∧
    ∀ (j : Fin r) (z : ℂ), (c : ℝ) * ‖z‖ ≤ 1 →
      (2 : ℝ) ^ p * ‖fxC p (v.getD j (0, 0)) - (c : ℂ) * z‖ <
        2 * c * ((2 : ℝ) ^ p * ‖fxC p (u.getD j (0, 0)) - z‖) + 3

/-- Per-element output condition as a predicate on values, in the form consumed by
`Work.ConvR.arrExtract`: the output value is a row `cvecVal v` and *every* preimage `u` of the input
satisfies `ArrErr`. -/
def ArrQ (p r c : ℕ) (x y : Val) : Prop :=
  ∃ v : List (ℤ × ℤ), y = cvecVal v ∧
    ∀ u : List (ℤ × ℤ), x = cvecVal u → ArrErr p r c u v

/-- Precondition of the array word on the value stack. -/
def ArrPre (p c : ℕ) (As : List (List (ℤ × ℤ))) (rest : List Val) : List Val → Prop :=
  fun vs => vs = rarrVal As :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest

/-- Postcondition of the array word on the value stack. -/
def ArrPost (p c r M : ℕ) (As : List (List (ℤ × ℤ))) (rest : List Val) : List Val → Prop :=
  fun out => ∃ Bs : List (List (ℤ × ℤ)),
    out = rarrVal Bs :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest ∧
    Bs.length = M ∧ ∀ i : ℕ, i < M → ArrErr p r c (As.getD i []) (Bs.getD i [])

/-- Every `Eval` costs at least one step. -/
theorem eval_cost_pos {main p : Cmd} {s s' : State} {n : ℕ} (h : Eval main p s s' n) : 1 ≤ n := by
  induction h with
  | skip => exact le_refl 1
  | pop => exact le_refl 1
  | peek => exact le_refl 1
  | push => exact le_refl 1
  | set => exact le_refl 1
  | mov => exact le_refl 1
  | seq _ _ ih1 ih2 => omega
  | iteT _ _ ih => omega
  | iteF _ _ ih => omega
  | loopF => exact le_refl 1
  | loopT _ _ ih1 ih2 => omega
  | self _ ih => omega

end Work.ConvR
