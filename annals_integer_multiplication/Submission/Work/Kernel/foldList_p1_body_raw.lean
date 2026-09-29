import Mathlib
import Submission.Work.Kernel.foldListDefs

open HvdH Work.Layout

set_option autoImplicit false

namespace Work.Kernel

/-- **One iteration of phase 1 of `Work.Kernel.foldList`, raw `Ev` form.**

`foldList_body1 = seqs [.pop 0 foldList_rS, mvVal 0 1 3 4, .peek 0 foldList_rG]`
(`Submission/Work/Kernel/foldListDefs.lean`).  Starting from a state whose stack `0` is headed by
`Glyph.cons` followed by `enc x` and then the remaining value stack `ofList rest :: acc` (above the
frame `R`), and whose stack `1` is `A0s`:

* the `pop` drops that leading `cons`;
* `mvVal 0 1 3 4` moves the exposed value `x` from stack `0` to the *top* of stack `1`
  (scratch stacks `3`, `4` restored, cost `≤ 16 * (vsz x + 1)`);
* the `peek` loads the new head of stack `0` — the first glyph of `ofList rest` — into
  `foldList_rG`, i.e. `nil` if `rest = []` and `cons` otherwise.

Total cost `≤ 16 * (L + 1) + 2` when `vsz x ≤ L`; stack `0` is left as `encs (ofList rest :: acc) ++ R`
and stack `1` as `x.enc ++ A0s`; every other stack is untouched. -/
theorem foldList_p1_body_raw (main : HvdH.Cmd) (X : HvdH.State) (x : HvdH.Val)
    (rest acc : List HvdH.Val) (R A0s : List HvdH.Glyph) (L : ℕ)
    (hv : HvdH.vsz x ≤ L)
    (h0 : X.stk 0 = HvdH.Glyph.cons :: (x.enc ++ (HvdH.encs (HvdH.ofList rest :: acc) ++ R)))
    (h1 : X.stk 1 = A0s) :
    ∃ X', Work.Layout.Ev main Work.Kernel.foldList_body1 X X' (16 * (L + 1) + 2) ∧
      X'.stk 0 = HvdH.encs (HvdH.ofList rest :: acc) ++ R ∧
      X'.stk 1 = x.enc ++ A0s ∧
      X'.reg Work.Kernel.foldList_rG =
        (if rest = [] then HvdH.Glyph.nil else HvdH.Glyph.cons) ∧
      (∀ k, k ≠ 0 → k ≠ 1 → X'.stk k = X.stk k) := by
  -- after the leading `pop`: stack 0 is `x.enc ++ (encs (ofList rest :: acc) ++ R)`, stack 1 is `A0s`
  have hP0 : Function.update X.stk 0 (X.stk 0).tail 0
      = x.enc ++ (HvdH.encs (HvdH.ofList rest :: acc) ++ R) := by
    rw [Function.update_self, h0]
    simp
  have hP1 : Function.update X.stk 0 (X.stk 0).tail 1 = A0s := by
    rw [Function.update_of_ne (show (1 : HvdH.Stk) ≠ 0 by decide), h1]
  -- the value mover: `x` moves from stack 0 to (the top of) stack 1
  obtain ⟨s', n, hmv, hnle, hs0, hs1, hs3, hs4, hfr⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update X.reg foldList_rS ((X.stk 0).headD .eos))
      (X := Function.update X.stk 0 (X.stk 0).tail) (v := x)
      (A := HvdH.encs (HvdH.ofList rest :: acc) ++ R) hP0 hP1
  -- the final `peek`
  have hpeek : Work.Layout.Ev main (.peek (0 : HvdH.Stk) foldList_rG) s'
      ⟨Function.update s'.reg foldList_rG ((s'.stk 0).headD .eos), s'.stk⟩ 1 :=
    ev_peek main 0 foldList_rG s'
  have hmvpeek : Work.Layout.Ev main
      (.seq (Work.Layout.mvVal (0 : HvdH.Stk) 1 3 4) (.peek (0 : HvdH.Stk) foldList_rG))
      ⟨Function.update X.reg foldList_rS ((X.stk 0).headD .eos),
        Function.update X.stk 0 (X.stk 0).tail⟩
      ⟨Function.update s'.reg foldList_rG ((s'.stk 0).headD .eos), s'.stk⟩ (n + 1) :=
    Work.Layout.Ev.seq hmv hpeek
  have hbody : Work.Layout.Ev main
      (.seq (.pop (0 : HvdH.Stk) foldList_rS)
        (.seq (Work.Layout.mvVal (0 : HvdH.Stk) 1 3 4) (.peek (0 : HvdH.Stk) foldList_rG))) X
      ⟨Function.update s'.reg foldList_rG ((s'.stk 0).headD .eos), s'.stk⟩ (1 + (n + 1)) :=
    Work.Layout.Ev.seq (ev_pop main 0 foldList_rS X) hmvpeek
  refine ⟨⟨Function.update s'.reg foldList_rG ((s'.stk 0).headD .eos), s'.stk⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- unfold `foldList_body1` and bound the cost
    have hmono : 1 + (n + 1) ≤ 16 * (L + 1) + 2 := by omega
    simpa [Work.Kernel.foldList_body1, Work.Kernel.foldList_rS, Work.Kernel.foldList_rG,
      Work.Layout.seqs] using hbody.mono hmono
  · exact hs0
  · exact hs1
  · show (Function.update s'.reg foldList_rG ((s'.stk 0).headD HvdH.Glyph.eos)) foldList_rG = _
    rw [Function.update_self, hs0]
    exact Work.Kernel.foldList_headD_ofList rest acc R
  · intro k hk0 hk1
    show s'.stk k = X.stk k
    by_cases hk3 : k = 3
    · rw [hk3, hs3, Function.update_of_ne (show (3 : HvdH.Stk) ≠ 0 by decide)]
    · by_cases hk4 : k = 4
      · rw [hk4, hs4, Function.update_of_ne (show (4 : HvdH.Stk) ≠ 0 by decide)]
      · rw [hfr k hk0 hk1 hk3 hk4, Function.update_of_ne hk0]

end Work.Kernel
