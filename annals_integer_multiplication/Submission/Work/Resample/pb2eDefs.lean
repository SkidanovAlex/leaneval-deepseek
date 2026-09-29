import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs
import Submission.Work.Resample.paBasic

/-!
# Definitions for the preamble of one `B̃` axis step (`Work.Resample.pb2StageE`)

This is the mirror of `Submission/Work/Resample/paStageDefs.lean` / `paEStageKc` / `paEStageCost`
for the `B̃` half of paper Theorem 4.1.  The stage program is the same sequence of library words as
in the `Ã` half; only the meaning of the stacks changes (`ss ↔ ts` swapped in the data flow,
stack 2 keeps the remaining *input* dims `ts.drop j`, stack 3 the remaining *output* dims
`ss.drop j`, stack 6 the running outer product `(ss.take j).prod`, stack 7 the stashed output
dimension `s_j` and stack 11 the stashed input dimension `t_j`), and the per-axis budget is
`PB2Br`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The cost constant of the `B̃` preamble: the sum of the per-phase constants of the eighteen
library words, plus `Kb` (for the preparation word `prep`). -/
def pb2EKc (K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f
    Kb : ℕ) : ℕ :=
  K1 + (3 * K5a + (K7 + (3 * K5b + (K11 + (Kpv + (7 * K6 * (D + 1) + (Kn10 + (Kc4a + (Kc4b +
    (Kc4c + (Kc4d + (1 + (Ku1 + (Kb10 + (Kc4e + (Kb11 + (Kc4f + Kb)))))))))))))))))

/-- The aggregate cost bound of the eighteen phases of the `B̃` preamble, in their order of
execution: park the array, peel `s_j` off stack 3, stash it on stack 7, peel `t_j` off stack 2,
stash it on stack 11, push `int 1`, fold the product `B_j = ∏_{k>j} t_k` of stack 2 into it, stash
`B_j` on stack 10, copy `t_j` (stack 11), copy `s_j` (stack 7), copy `α` (stack 4), copy `p`
(stack 5), run `prep`, unpark the array on top of the table, move `B_j` from stack 10, copy `s_j`
(stack 7), move `t_j` from stack 11, copy `A_j = ∏_{k<j} s_k` (stack 6). -/
def pb2ECost (K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f
    Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) (arr : Val) : ℕ :=
  K1 * (vsz arr + 1) + (K5a * (vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j +
    1)))) + vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (K7 * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) +
    (K5b * (vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) + vsz
    (Val.int (ts.getD j 0 : ℤ)) + 1) + (K11 * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) + (Kpv *
    (vsz (Val.int 1) + 1) + (K6 * ((ts.drop (j + 1)).length + 1) * ((((ts.drop (j + 1)).map (fun
    x : ℕ => isz (x : ℤ))).sum) + ((ts.drop (j + 1)).prod).size + 2) * (((ts.drop (j +
    1)).prod).size + 2) + (Kn10 * (vsz (Val.int ((ts.drop (j + 1)).prod)) + 1) + (Kc4b * (vsz
    (Val.int (ts.getD j 0 : ℤ)) + 1) + (Kc4a * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (Kc4c *
    (vsz (Val.int α) + 1) + (Kc4d * (vsz (Val.int p) + 1) + (1 * (Kb * (ts.getD j 0 + 1) * (p +
    1) ^ Kb) + (Ku1 * (vsz arr + 1) + (Kb10 * (vsz (Val.int ((ts.drop (j + 1)).prod)) + 1) +
    (Kc4e * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) + (Kb11 * (vsz (Val.int (ts.getD j 0 : ℤ)) +
    1) + (Kc4f * (vsz (Val.int ((ss.take j).prod)) + 1))))))))))))))))))

/-- `SliceSpecAt` with `Kb = 0` is contradictory: the cost bound `0` of the preparation word is
smaller than the smallest possible `Eval` cost. -/
theorem pb2EKb0False {Kb : ℕ} (hKb0 : Kb = 0) {p α s t : ℕ} {prep q : Cmd}
    {Φ : (Fin t → ℤ × ℤ) → (Fin s → ℤ × ℤ)} {Pj : List Val}
    (h : SliceSpecAt prep q Kb p α s t Φ Pj)
    (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ) (hmon : Monotone Cm) (hmb : MulBelow main N Cm)
    (hN : Kb * p < N) : False := by
  obtain ⟨hprep, -, -, -⟩ := h
  obtain ⟨out, s', n, -, hev, hc, -⟩ :=
    hprep main N Cm hmon hmb hN [Val.int p, Val.int α, Val.int s, Val.int t] ⟨[], rfl⟩
      ⟨fun _ => Glyph.eos, fun k => if k = 0 then encs [Val.int p, Val.int α, Val.int s, Val.int t]
        else []⟩ [] (by simp)
  have hpos : 1 ≤ n := paEvalPos hev
  rw [hKb0] at hc
  simp at hc
  omega

end Work.Resample
