import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.divRaw

/-!
# IntLib division: the core computation

Definitions and specifications of the long-division core assembled in `Work.IntLib.divWord`.
Everything here lives in the namespace `Work.IntLib.Div`, because other agents work in
`Work.IntLib` at the same time.

Stack cache (markers `gP … gY` from `divRaw`):

| stack | role |
|-------|------|
| 0 | value stack (`z` below the two operands) |
| 1 | pending dividend bits (most significant first) |
| 2 | divisor, `L` bits, least significant first |
| 3 | remainder, `L` bits, least significant first |
| 4 | quotient bits, least significant first |
| 5 | ripple result |
| 6 | ripple copy of the divisor |
| 7 | ripple copy of the remainder |
| 8 | reversal / stripping scratch |
| 9 | sign glyphs |

Register discipline: every program sets the registers it reads.  Marker discipline: a program
starts and ends with every stack of the cache of the form `region ++ marker :: b0.stk k`; the
helpers `dropReg`/`mkG` maintain this.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib.Div

open HvdH

/-! ## Stack and register names -/

abbrev stP : Stk := 1
abbrev stB : Stk := 2
abbrev stR : Stk := 3
abbrev stQ : Stk := 4
abbrev stS : Stk := 5
abbrev stC : Stk := 6
abbrev stD : Stk := 7
abbrev stX : Stk := 8
abbrev stY : Stk := 9

abbrev rgB : Reg := 2
abbrev rgC : Reg := 3
abbrev rgS : Reg := 4
abbrev rgT : Reg := 5
abbrev rgU : Reg := 6
abbrev rgV : Reg := 7
abbrev rgW : Reg := 8

/-- Sequence a list of commands (the trailing `skip` costs one step, which the cost bounds absorb). -/
def seqs (l : List Cmd) : Cmd := l.foldr Cmd.seq .skip

@[simp] theorem seqs_nil : seqs [] = .skip := rfl
@[simp] theorem seqs_cons (c : Cmd) (cs : List Cmd) : seqs (c :: cs) = .seq c (seqs cs) := rfl

theorem eval_seqs_cons {main : Cmd} {c : Cmd} {cs : List Cmd} {s s₁ s' : State} {n₁ n : ℕ}
    (h₁ : Eval main c s s₁ n₁) (h₂ : Eval main (seqs cs) s₁ s' n) :
    Eval main (seqs (c :: cs)) s s' (n₁ + n) :=
  Eval.seq h₁ h₂

/-! ## Generic state with explicit stack contents -/

/-- The state in which stacks 0–9 hold the given glyph lists, while stacks 10–15 and all registers
come from `b0`. -/
def gSt (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) : State :=
  State.updStk (State.updStk (State.updStk (State.updStk (State.updStk (State.updStk
  (State.updStk (State.updStk (State.updStk (State.updStk b0 0 c0)
    1 c1) 2 c2) 3 c3) 4 c4) 5 c5) 6 c6) 7 c7) 8 c8) 9 c9

@[simp] theorem gSt_stk0 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 0 = c0 := by simp [gSt]
@[simp] theorem gSt_stk1 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 1 = c1 := by simp [gSt]
@[simp] theorem gSt_stk2 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 2 = c2 := by simp [gSt]
@[simp] theorem gSt_stk3 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 3 = c3 := by simp [gSt]
@[simp] theorem gSt_stk4 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 4 = c4 := by simp [gSt]
@[simp] theorem gSt_stk5 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 5 = c5 := by simp [gSt]
@[simp] theorem gSt_stk6 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 6 = c6 := by simp [gSt]
@[simp] theorem gSt_stk7 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 7 = c7 := by simp [gSt]
@[simp] theorem gSt_stk8 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 8 = c8 := by simp [gSt]
@[simp] theorem gSt_stk9 (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk 9 = c9 := by simp [gSt]

theorem gSt_stk_hi (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) (j : Stk)
    (hj : 10 ≤ j.val) : (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).stk j = b0.stk j := by
  have h0 : j ≠ 0 := by intro h; rw [h] at hj; simp at hj
  have h1 : j ≠ 1 := by intro h; rw [h] at hj; simp at hj
  have h2 : j ≠ 2 := by intro h; rw [h] at hj; simp at hj
  have h3 : j ≠ 3 := by intro h; rw [h] at hj; simp at hj
  have h4 : j ≠ 4 := by intro h; rw [h] at hj; simp at hj
  have h5 : j ≠ 5 := by intro h; rw [h] at hj; simp at hj
  have h6 : j ≠ 6 := by intro h; rw [h] at hj; simp at hj
  have h7 : j ≠ 7 := by intro h; rw [h] at hj; simp at hj
  have h8 : j ≠ 8 := by intro h; rw [h] at hj; simp at hj
  have h9 : j ≠ 9 := by intro h; rw [h] at hj; simp at hj
  simp [gSt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

@[simp] theorem gSt_reg (b0 : State) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : List Glyph) (r : Reg) :
    (gSt b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).reg r = b0.reg r := rfl

/-- The canonical state of the long-division core. -/
def fullSt (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) : State :=
  gSt b0 z (bitsG p ++ [gP]) (bitsG b ++ [gB]) (bitsG r ++ [gR]) (bitsG q ++ [gQ])
    (bitsG s5 ++ [gS]) (bitsG s6 ++ [gC]) (bitsG s7 ++ [gD]) (bitsG s8 ++ [gX]) (Y ++ [gY])

/-- `fullSt` with the loop register set. -/
def fullStR (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) (g : Glyph) : State :=
  (fullSt b0 z Y p b r q s5 s6 s7 s8).updReg rLoop g

@[simp] theorem fullSt_stk1 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stP = bitsG p ++ [gP] := by simp [fullSt, stP]
@[simp] theorem fullSt_stk2 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stB = bitsG b ++ [gB] := by simp [fullSt, stB]
@[simp] theorem fullSt_stk3 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stR = bitsG r ++ [gR] := by simp [fullSt, stR]
@[simp] theorem fullSt_stk4 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stQ = bitsG q ++ [gQ] := by simp [fullSt, stQ]
@[simp] theorem fullSt_stk5 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stS = bitsG s5 ++ [gS] := by simp [fullSt, stS]
@[simp] theorem fullSt_stk6 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stC = bitsG s6 ++ [gC] := by simp [fullSt, stC]
@[simp] theorem fullSt_stk7 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stD = bitsG s7 ++ [gD] := by simp [fullSt, stD]
@[simp] theorem fullSt_stk8 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stX = bitsG s8 ++ [gX] := by simp [fullSt, stX]
@[simp] theorem fullSt_stk9 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk stY = Y ++ [gY] := by simp [fullSt, stY]
@[simp] theorem fullSt_stk0 (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool) :
    (fullSt b0 z Y p b r q s5 s6 s7 s8).stk 0 = z := by simp [fullSt, gSt]
@[simp] theorem fullSt_stk_hi (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool)
    (j : Stk) (hj : 10 ≤ j.val) : (fullSt b0 z Y p b r q s5 s6 s7 s8).stk j = b0.stk j := by
  simp only [fullSt]
  exact gSt_stk_hi _ _ _ _ _ _ _ _ _ _ _ j hj
@[simp] theorem fullStR_reg_loop (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool)
    (g : Glyph) : (fullStR b0 z Y p b r q s5 s6 s7 s8 g).reg rLoop = g := by simp [fullStR]
@[simp] theorem fullStR_stk (b0 : State) (z Y : List Glyph) (p b r q s5 s6 s7 s8 : List Bool)
    (g : Glyph) (j : Stk) : (fullStR b0 z Y p b r q s5 s6 s7 s8 g).stk j =
      (fullSt b0 z Y p b r q s5 s6 s7 s8).stk j := by simp [fullStR]

/-! ## Programs -/

/-- Push a marker `m` onto stack `k` (register `rgT` is clobbered). -/
def mkG (k : Stk) (m : Glyph) : Cmd := .seq (.set rgT m) (.push k rgT)

/-- Push the nine markers `gP … gY` onto stacks 1–9. -/
def pushMarkers : Cmd :=
  seqs [mkG stP gP, mkG stB gB, mkG stR gR, mkG stQ gQ, mkG stS gS, mkG stC gC, mkG stD gD,
        mkG stX gX, mkG stY gY]

/-- Handler of `extract` for the divisor: push the bit onto stack 8, a zero onto stack 3. -/
def extractBHandler : Cmd :=
  seqs [.push stX rLoop, .set rgS (Glyph.bit false), .push stR rgS]

/-- Consume the two operands of stack 0: sign glyphs onto stack 9, dividend bits onto stack 1,
divisor bits (with the padding zero) onto stack 2, `L` zeros onto stack 3. -/
def extract : Cmd :=
  seqs [.pop 0 rgT, .push stY rgT, consume 0 Glyph.iend rLoop (.push stP rLoop),
        .pop 0 rLoop, .pop 0 rgT, .push stY rgT,
        consume 0 Glyph.iend rLoop extractBHandler, .pop 0 rLoop,
        .set rgS (Glyph.bit false), .push stR rgS,
        .set rgS (Glyph.bit false), .push stX rgS, mvRevOnto stX gX stB rgT, mkG stX gX]

/-- One shift of the remainder: push the dividend bit (in `rLoop`) onto stack 3 and drop the bottom
bit (the padding zero at the most significant end). -/
def shiftR : Cmd :=
  seqs [.push stR rLoop, mvRevOnto stR gR stX rgT, .pop stX rgT,
        mvRev stX gX stR gR rgT, mkG stX gX]

/-- Body of the ripple loop: pop a bit from the second region, save both operand bits, run the
subtraction step, push the result bit onto stack 5. -/
def rippleBody (sb : Stk) : Cmd :=
  seqs [.pop sb rgB, .push stC rgB, .push stD rLoop, subBitProg rLoop rgB rgC rgS, .push stS rgS]

/-- Ripple subtraction of the region of stack `sa` (marker `ma`) by that of stack `sb` (marker
`mb`), both of length `L`: copies (reversed) onto stacks 7 and 6, the result (reversed) onto stack
5, the final borrow in `rgC`; the two input regions and markers are removed. -/
def rippleProg (sa sb : Stk) (ma mb : Glyph) : Cmd :=
  seqs [.set rgC (Glyph.bit false), consume sa ma rLoop (rippleBody sb),
        .pop sa rLoop, .pop sb rgB]

/-- Ripple specialised to the main loop (`sa = stR`, `sb = stB`). -/
def rippleMain : Cmd := rippleProg stR stB gR gB

/-- Drop a region but keep its marker. -/
def dropReg (k : Stk) (T : Glyph) (r : Reg) : Cmd := consume k T r .skip

/-- The per-iteration work of the main loop (the dividend bit is in `rLoop`). -/
def mainWork : Cmd :=
  seqs [shiftR, rippleMain,
        mvRev stC gC stB gB rgT, mkG stC gC,
        .ite rgC (Glyph.bit true)
          (seqs [.set rgS (Glyph.bit false), .push stQ rgS])
          (seqs [.set rgS (Glyph.bit true), .push stQ rgS]),
        .ite rgC (Glyph.bit true)
          (seqs [mvRev stD gD stR gR rgT, mkG stD gD, dropReg stS gS rgU])
          (seqs [mvRev stS gS stR gR rgT, mkG stS gS, dropReg stD gD rgU])]

/-- One iteration of the main loop. -/
def mainStep : Cmd :=
  seqs [.pop stP rLoop,
        .ite rLoop gP
          (seqs [.push stP rLoop, .set rLoop (Glyph.mk 0)])
          (seqs [mainWork, .set rLoop Glyph.eos])]

/-- The main loop over the dividend bits. -/
def mainLoopProg : Cmd := seqs [.set rLoop Glyph.eos, .loop rLoop Glyph.eos mainStep]

/-- The whole core: markers, extraction, long division. -/
def coreProg : Cmd := seqs [pushMarkers, extract, mainLoopProg]

/-! ## Fix-ups -/

/-- Move the (possibly zero padded, least significant first) region of stack `src` to stack 8
(reversed, leading zeros stripped) and restore the empty marker of `src`. -/
def prep (src : Stk) (msrc : Glyph) : Cmd :=
  seqs [mvRevOnto src msrc stX rgT, stripZeros stX gX rgT, mkG src msrc]

/-- Push the `iend`, move the stripped region of stack 8 onto stack 0, push the sign glyph in `sg`. -/
def emit (sg : Reg) : Cmd :=
  seqs [.set rgT Glyph.iend, .push 0 rgT, mvRevOnto stX gX 0 rgT, mkG stX gX,
        .mov rgT sg, .push 0 rgT]

/-- Drop all nine regions and their markers. -/
def cleanup : Cmd :=
  seqs [dropRgn stP gP rgT, dropRgn stB gB rgT, dropRgn stR gR rgT, dropRgn stQ gQ rgT,
        dropRgn stS gS rgT, dropRgn stC gC rgT, dropRgn stD gD rgT, dropRgn stX gX rgT,
        dropRgn stY gY rgT]

/-- Read the two sign glyphs: divisor sign in `rgT`, dividend sign in `rgU`. -/
def readSigns : Cmd := seqs [.pop stY rgT, .pop stY rgU]

/-- Fix-up for `Int.tdiv`.  The sign of the quotient is the product of the two operand signs, so
the nested `ite` on `rgU` (dividend sign) and `rgT` (divisor sign) must run *before* `prep stQ gQ`:
the trailing `mkG stQ gQ` of `prep` clobbers `rgT` with the marker `gQ`, which silently killed the
divisor-sign test in an earlier version of this program. -/
def fixTdiv : Cmd :=
  seqs [readSigns,
        .ite rgU Glyph.neg
          (.ite rgT Glyph.neg (.set rgW Glyph.pos) (.set rgW Glyph.neg))
          (.ite rgT Glyph.neg (.set rgW Glyph.neg) (.set rgW Glyph.pos)),
        prep stQ gQ,
        .peek stX rgV, .ite rgV gX (.set rgW Glyph.pos) .skip,
        emit rgW, cleanup]

/-- Fix-up for `Int.tmod`. -/
def fixTmod : Cmd :=
  seqs [readSigns, prep stR gR,
        .ite rgU Glyph.neg (.set rgW Glyph.neg) (.set rgW Glyph.pos),
        .peek stX rgV, .ite rgV gX (.set rgW Glyph.pos) .skip,
        emit rgW, cleanup]

/-- Fix-up for `Int.fdiv`. -/
def fixFdiv : Cmd :=
  seqs [readSigns,
        .ite rgU Glyph.neg
          (seqs [mvRevOnto stR gR stD rgT, stripZeros stD gD rgT, .peek stD rgV,
                 .ite rgV gD .skip (incBits stQ gQ stX gX rgT rgV),
                 mvRev stD gD stR gR rgT, mkG stD gD, prep stQ gQ,
                 .set rgW Glyph.neg, emit rgW, cleanup])
          (seqs [prep stQ gQ, .set rgW Glyph.pos, emit rgW, cleanup])]

/-- Fix-up for `Int.fmod`. -/
def fixFmod : Cmd :=
  seqs [readSigns,
        .ite rgU Glyph.neg
          (seqs [rippleProg stB stR gB gR, mkG stB gB, mkG stR gR, stripZeros stC gC rgT,
                 .peek stC rgV,
                 .ite rgV gC
                   (seqs [.set rgV Glyph.iend, .push 0 rgV,
                          .set rgT Glyph.pos, .push 0 rgT, cleanup])
                   (seqs [mvRevOnto stS gS stR rgT, mkG stS gS, prep stR gR,
                          .set rgW Glyph.pos, emit rgW, cleanup])])
          (seqs [prep stR gR, .set rgW Glyph.pos, emit rgW, cleanup])]

end Work.IntLib.Div
