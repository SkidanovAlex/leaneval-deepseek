import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.evChainDefs
import Submission.Work.IntLib.evChainLoop
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base

namespace Work.IntLib

open HvdH
open Work.Layout

/-- The cost of one chain entry splits into a term proportional to the size of the entry and a
constant: `Σ (KR * (size + 2)) = KR * Σ size + 2 * KR * length`. -/
theorem sum_size_add_two (t : List ℕ) (KR : ℕ) :
    (t.map (fun h => KR * (h.size + 2))).sum = KR * (t.map (fun h => h.size)).sum + 2 * KR * t.length := by
  induction t with
  | nil => simp
  | cons h t ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.length_cons, ih]
    ring

theorem evChainMove (k : HvdH.Stk) (hk : k ≠ (0 : HvdH.Stk)) (readG : HvdH.Cmd) (KR : ℕ)
    (hread : ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
      (h : ℕ) (rest : List HvdH.Glyph),
      X 0 = HvdH.Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main readG ⟨g, X⟩ s' n ∧
        n ≤ KR * (h.size + 2) ∧ s'.stk 0 = rest ∧
        s'.stk k = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ X k ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ k → s'.stk j = X j)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph) (hs : List ℕ) (rest : List HvdH.Glyph),
      X 0 = HvdH.Val.enc (HvdH.intList hs) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧
        n ≤ K * ((hs.map fun h => h.size).sum + hs.length + 1) ∧
        s'.stk 0 = rest ∧
        s'.stk k = (HvdH.Val.enc (HvdH.intList hs)).reverse ++ X k ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ k → s'.stk j = X j) := by
  refine ⟨evChainProg k readG, 2 * KR + 12, ?_⟩
  intro main g X hs rest hX
  -- the stack functions before and after the loop
  let F0 : Stk → List Glyph := fun j => if j = 0 then Val.enc (intList hs) ++ rest
    else if j = k then ([] : List Glyph) ++ X k else X j
  let F1 : Stk → List Glyph := fun j => if j = 0 then [Glyph.nil] ++ rest
    else if j = k then revAcc hs ++ ([] : List Glyph) ++ X k else X j
  have hF0X : F0 = X := by
    funext j
    dsimp only [F0]
    by_cases h0 : j = 0
    · rw [if_pos h0, h0]; exact hX.symm
    · rw [if_neg h0]
      by_cases h1 : j = k
      · rw [if_pos h1, h1]; simp
      · rw [if_neg h1]
  -- run the loop
  obtain ⟨gm', _hfl, hloop⟩ := evChainLoop k hk readG KR hread main hs ([] : List Glyph) rest X
    (Function.update g rLp fGo) (Function.update_self rLp fGo g)
  have hloopF : Ev main (evChainLoopP k readG) ⟨Function.update g rLp fGo, F0⟩ ⟨gm', F1⟩
      (8 * hs.length + 5 + (hs.map (fun h => KR * (h.size + 2))).sum) := hloop
  have hloopX : Ev main (evChainLoopP k readG) ⟨Function.update g rLp fGo, X⟩ ⟨gm', F1⟩
      (8 * hs.length + 5 + (hs.map (fun h => KR * (h.size + 2))).sum) := by
    rw [show (⟨Function.update g rLp fGo, F0⟩ : State) = ⟨Function.update g rLp fGo, X⟩ from
      by rw [hF0X]] at hloopF
    exact hloopF
  -- the head of stack 0 after the loop
  have hF1_0 : F1 0 = Glyph.nil :: rest := by
    dsimp only [F1]
    simp
  -- move the final `nil` from stack 0 to stack k
  have hset : Ev main (.set rLp fGo) ⟨g, X⟩ ⟨Function.update g rLp fGo, X⟩ 1 :=
    ev_set main rLp fGo ⟨g, X⟩
  have hpop0 : Ev main (.pop 0 rX) ⟨gm', F1⟩
      ⟨Function.update gm' rX ((F1 0).headD .eos), Function.update F1 0 ((F1 0).tail)⟩ 1 :=
    ev_pop main 0 rX ⟨gm', F1⟩
  simp only [hF1_0, List.headD_cons, List.tail_cons] at hpop0
  have hpush0 : Ev main (.push k rX)
      ⟨Function.update gm' rX Glyph.nil, Function.update F1 0 rest⟩
      ⟨Function.update gm' rX Glyph.nil,
       Function.update (Function.update F1 0 rest) k
         ((Function.update gm' rX Glyph.nil) rX :: (Function.update F1 0 rest) k)⟩ 1 :=
    ev_push main k rX ⟨Function.update gm' rX Glyph.nil, Function.update F1 0 rest⟩
  -- the final state
  let gm3 : Reg → Glyph := Function.update gm' rX Glyph.nil
  let F3 : Stk → List Glyph := Function.update (Function.update F1 0 rest) k
    (gm3 rX :: (Function.update F1 0 rest) k)
  have hseg3 : Ev main (.seq (.pop 0 rX) (.push k rX)) ⟨gm', F1⟩ ⟨gm3, F3⟩ (1 + 1) :=
    Ev.seq hpop0 hpush0
  have hseg2 : Ev main (.seq (evChainLoopP k readG) (.seq (.pop 0 rX) (.push k rX)))
      ⟨Function.update g rLp fGo, X⟩ ⟨gm3, F3⟩
      ((8 * hs.length + 5 + (hs.map (fun h => KR * (h.size + 2))).sum) + (1 + 1)) :=
    Ev.seq hloopX hseg3
  have hall : Ev main (evChainProg k readG) ⟨g, X⟩ ⟨gm3, F3⟩
      (1 + ((8 * hs.length + 5 + (hs.map (fun h => KR * (h.size + 2))).sum) + (1 + 1))) :=
    Ev.seq hset hseg2
  obtain ⟨n, hev, hn⟩ := hall
  refine ⟨⟨gm3, F3⟩, n, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨n, hev, le_rfl⟩
  · -- cost bound
    have hsum : (hs.map (fun h => KR * (h.size + 2))).sum
        = KR * (hs.map (fun h => h.size)).sum + 2 * KR * hs.length := sum_size_add_two hs KR
    rw [hsum] at hn
    set S := (hs.map (fun h => h.size)).sum with hS
    set m := hs.length with hm
    nlinarith
  · -- stack 0
    dsimp only [F3]
    rw [Function.update_of_ne (show (0 : Stk) ≠ k from fun h => hk h.symm)]
    exact Function.update_self 0 rest F1
  · -- stack k
    have hF1k : F1 k = revAcc hs ++ X k := by
      dsimp only [F1]
      simp [hk]
    dsimp only [F3]
    rw [Function.update_self]
    have hgm3 : gm3 rX = Glyph.nil := by
      dsimp only [gm3]
      exact Function.update_self rX Glyph.nil gm'
    rw [hgm3, Function.update_of_ne (show k ≠ 0 from hk), hF1k]
    rw [rev_enc_intList hs, List.cons_append]
  · -- all other stacks
    intro j hj0 hjk
    dsimp only [F3]
    rw [Function.update_of_ne (show j ≠ k from hjk),
      Function.update_of_ne (show j ≠ 0 from hj0)]
    dsimp only [F1]
    simp only [if_neg hj0, if_neg hjk]

end Work.IntLib
