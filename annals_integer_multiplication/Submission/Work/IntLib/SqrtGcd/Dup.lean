import Submission.Work.IntLib.SqrtGcd.Basic

/-!
# Duplicating a bit region

`cLoop2 k T d1 d2 r` pops the region above the marker `T` of stack `k` and pushes every glyph onto
*both* `d1` and `d2` (so both receive the reversal of the region; `k` keeps `T :: below`).

`dup2 src dst t1 t2 r` uses `cLoop2` (one pass) and four reversal moves to duplicate the region of
`src` onto `dst`, **keeping `src` intact**; `t1`, `t2` are (empty) scratch stacks.  Note that a
sequence of `rLoop` (reverse *move*) operations alone cannot duplicate: a move empties its source.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

/-- One step of the two-destination loop. -/
def cBody2 (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg) : Cmd :=
  .seq (.pop k r)
    (.ite r T (.seq (.push k r) (.set r T))
      (.seq (.push d1 r) (.seq (.push d2 r) (.set r Glyph.eos))))

def cLoop2 (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg) : Cmd :=
  .seq (.set r Glyph.eos) (.loop r Glyph.eos (cBody2 k T d1 d2 r))

/-- Result state of `cLoop2`. -/
def c2St (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg) (gs below : List Glyph) (s : State) :
    State :=
  ⟨Function.update s.reg r T,
    Function.update (Function.update (Function.update s.stk k (T :: below)) d1
      (gs.reverse ++ s.stk d1)) d2 (gs.reverse ++ s.stk d2)⟩

/-- Duplicate the region of `src` onto `dst`, keeping `src`; `t1`, `t2` are scratch. -/
def dup2 (src dst t1 t2 : Stk) (r : Reg) : Cmd :=
  seqs [ cLoop2 src (.mk src) t1 t2 r,
         rLoop t1 (.mk t1) (some src) r,
         rLoop t2 (.mk t2) (some t1) r,
         rLoop t1 (.mk t1) (some t2) r,
         rLoop t2 (.mk t2) (some dst) r ]

/-- Result state of `dup2`. -/
def dupSt (src dst t1 t2 : Stk) (r : Reg) (gs : List Bool) (s : State) : State :=
  ⟨Function.update s.reg r (Glyph.mk t2), Function.update s.stk dst (gs.map Glyph.bit ++ s.stk dst)⟩

end SG
end Work.IntLib
