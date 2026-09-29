import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.eval_mvRev

/-!
# `IntLib` division: one shift of the remainder (`Div.shiftR`)

`Div.shiftR` is the first command of the body of the long-division main loop
(`Div.mainWork`).  With the remainder region of stack `stR` holding the `L` bits of `r`
(least significant first, `r.getLast? = some false` — the padding zero) it

1. pushes the new low bit `d` (taken from the loop register `rLoop`) onto that region,
2. reverses the region onto the scratch stack `stX` (above its marker `gX`),
3. pops one glyph: the padding zero, which the reversal of step 2 has brought to the top,
4. reverses the rest back onto `stR` (below a fresh marker `gR`),
5. restores the marker of `stX`.

The result is the `L`-bit window shifted left by one bit (`Div.shiftBits d L r = d :: r.take (L-1)`),
at cost `12 * (L+1) + 42 ≤ 12 * (L+1) + 40` — the statement `div_shiftR` below.

The proof is split into the two pieces of the program that are literally sub-programs of
`Div.shiftR`: `div_shiftR_pop` (step 3, which contains the list identity
`(bitsG (d :: r)).reverse = bit false :: ((bitsG (r.take (L-1))).reverse ++ [bit d])`) and
`div_shiftR_mvRev` (steps 4 and 5).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.IntLib

open HvdH

/-- Reading an updated stack at a different index. -/
theorem upd_stk_of_ne {s : State} {k j : Stk} (h : j ≠ k) (v : List Glyph) :
    (⟨s.reg, Function.update s.stk k v⟩ : State).stk j = s.stk j :=
  Function.update_of_ne (f := s.stk) h v

/-- Step 3 of `Div.shiftR`: the top glyph of the reversed remainder region is the padding zero
`Glyph.bit false` (because `r.getLast? = some false` and `r` is non-empty), so popping it leaves
`(bitsG (r.take (L-1))).reverse ++ [bit d]` above the marker of `stX`. -/
theorem div_shiftR_pop (main : HvdH.Cmd) (b0 : HvdH.State) (d : Bool) (r : List Bool) (L : ℕ)
    (hr : r.length = L) (hl : r.getLast? = some false) (S : HvdH.State)
    (hX : S.stk Work.IntLib.Div.stX =
      (Work.IntLib.bitsG (d :: r)).reverse ++ [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX) :
    ∃ s', HvdH.Eval main (HvdH.Cmd.pop Work.IntLib.Div.stX Work.IntLib.Div.rgT) S s' 1 ∧
      s'.stk Work.IntLib.Div.stX =
        ((Work.IntLib.bitsG (r.take (L - 1))).reverse ++ [HvdH.Glyph.bit d]) ++ [Work.IntLib.gX]
          ++ b0.stk Work.IntLib.Div.stX ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.Div.stX → s'.stk j = S.stk j) := by
  obtain ⟨r', hr'⟩ := List.getLast?_eq_some_iff.mp hl
  -- `r = r' ++ [false]`, so `r.take (L-1) = r'`
  have htake : r.take (L - 1) = r' := by
    have hlen : L - 1 = r'.length := by
      have h : r.length = r'.length + 1 := by rw [hr']; simp
      omega
    rw [hlen, hr']
    exact List.take_left' rfl
  -- the reversal brings the padding zero to the top
  have hhead : (bitsG (d :: r)).reverse =
      Glyph.bit false :: ((bitsG r').reverse ++ [Glyph.bit d]) := by
    rw [hr']
    simp [bitsG]
  have hsplit : S.stk Div.stX =
      Glyph.bit false :: (((bitsG r').reverse ++ [Glyph.bit d]) ++ [gX] ++ b0.stk Div.stX) := by
    rw [hX, hhead]
    rfl
  refine ⟨⟨Function.update S.reg Div.rgT (Glyph.bit false),
      Function.update S.stk Div.stX
        (((bitsG r').reverse ++ [Glyph.bit d]) ++ [gX] ++ b0.stk Div.stX)⟩, ?_, ?_, ?_⟩
  · exact Eval.pop_cons hsplit
  · show Function.update S.stk Div.stX
        (((bitsG r').reverse ++ [Glyph.bit d]) ++ [gX] ++ b0.stk Div.stX) Div.stX = _
    rw [Function.update_self, ← htake]
  · intro j hj
    show Function.update S.stk Div.stX
        (((bitsG r').reverse ++ [Glyph.bit d]) ++ [gX] ++ b0.stk Div.stX) j = S.stk j
    exact upd_stk_of_ne hj _

/-- Steps 4 and 5 of `Div.shiftR`: reverse the scratch region of `stX` (of length `l.length`) back
onto the (empty) region of `stR`, below a fresh marker `gR`, and restore the marker `gX` of `stX`. -/
theorem div_shiftR_mvRev (main : HvdH.Cmd) (b0 : HvdH.State) (l : List HvdH.Glyph) (S : HvdH.State)
    (hT : ∀ g ∈ l, g ≠ Work.IntLib.gX)
    (hX : S.stk Work.IntLib.Div.stX = l ++ [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX)
    (hR : S.stk Work.IntLib.Div.stR = b0.stk Work.IntLib.Div.stR) :
    ∃ s' n, HvdH.Eval main
        (HvdH.Cmd.seq (Work.IntLib.mvRev Work.IntLib.Div.stX Work.IntLib.gX Work.IntLib.Div.stR
            Work.IntLib.gR Work.IntLib.Div.rgT)
          (HvdH.Cmd.seq (Work.IntLib.Div.mkG Work.IntLib.Div.stX Work.IntLib.gX) HvdH.Cmd.skip))
        S s' n ∧
      n ≤ 6 * (l.length + 1) + 15 ∧
      s'.stk Work.IntLib.Div.stR = l.reverse ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR ∧
      s'.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.Div.stR → j ≠ Work.IntLib.Div.stX → s'.stk j = S.stk j) := by
  have hne : Div.stX ≠ Div.stR := by decide
  have hk : S.stk Div.stX = l ++ gX :: b0.stk Div.stX := by
    rw [hX, List.append_assoc]
    rfl
  obtain ⟨S1, n1, h1, hn1, hS1X, hS1R, hfr1⟩ :=
    eval_mvRev main Div.stX gX Div.stR gR Div.rgT l (b0.stk Div.stX) (b0.stk Div.stR) S
      hT hk hR hne
  -- `Div.mkG stX gX` = `set rgT gX; push stX rgT`, then the trailing `skip` of `seqs`
  let S1b : State := ⟨Function.update S1.reg Div.rgT gX, S1.stk⟩
  have hset : Eval main (.set Div.rgT gX) S1 S1b 1 := Eval.set_eq
  let S2 : State :=
    ⟨Function.update S1.reg Div.rgT gX, Function.update S1.stk Div.stX (gX :: S1.stk Div.stX)⟩
  have hpush : Eval main (.push Div.stX Div.rgT) S1b S2 1 := by
    have h := Eval.push (main := main) Div.stX Div.rgT S1b
    simpa [S1b, S2] using h
  have hskip : Eval main .skip S2 S2 1 := Eval.skip S2
  have hmk : Eval main (Div.mkG Div.stX gX) S1 S2 2 := Eval.seq hset hpush
  refine ⟨S2, n1 + (2 + 1), ?_, by omega, ?_, ?_, ?_⟩
  · have h := Eval.seq h1 (Eval.seq hmk hskip)
    simpa using h
  · have h2r : S2.stk Div.stR = S1.stk Div.stR :=
      upd_stk_of_ne (by decide : Div.stR ≠ Div.stX) (gX :: S1.stk Div.stX)
    rw [h2r, hS1R, List.append_assoc]
    rfl
  · have h2x : S2.stk Div.stX = gX :: S1.stk Div.stX :=
      Function.update_self Div.stX (gX :: S1.stk Div.stX) S1.stk
    rw [h2x, hS1X]
    rfl
  · intro j hjR hjX
    have h2j : S2.stk j = S1.stk j := upd_stk_of_ne hjX (gX :: S1.stk Div.stX)
    rw [h2j]
    exact hfr1 j hjX hjR

theorem div_shiftR (main : HvdH.Cmd) (b0 : HvdH.State) (d : Bool) (r : List Bool) (L : ℕ)
    (hr : r.length = L) (hl : r.getLast? = some false) (S : HvdH.State)
    (hR : S.stk Work.IntLib.Div.stR = Work.IntLib.bitsG r ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR)
    (hX : S.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX)
    (hrl : S.reg Work.IntLib.rLoop = HvdH.Glyph.bit d)
    (hoth : ∀ j : HvdH.Stk, j ≠ Work.IntLib.Div.stR → j ≠ Work.IntLib.Div.stX → S.stk j = b0.stk j) :
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.shiftR S s' n ∧ n ≤ 12 * (L + 1) + 40 ∧
      s'.stk Work.IntLib.Div.stR = Work.IntLib.bitsG (d :: r.take (L - 1)) ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR ∧
      s'.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.Div.stR → j ≠ Work.IntLib.Div.stX → s'.stk j = S.stk j) := by
  have hneRX : Div.stR ≠ Div.stX := by decide
  have hneXR : Div.stX ≠ Div.stR := by decide
  have hrne : r ≠ [] := by intro h; rw [h] at hl; simp at hl
  have hL1 : 1 ≤ L := by have := List.length_pos_iff.mpr hrne; omega
  -- step 1: push the new low bit `d` onto the remainder region
  let S1 : State := ⟨S.reg, Function.update S.stk Div.stR (Glyph.bit d :: S.stk Div.stR)⟩
  have h1 : Eval main (.push Div.stR rLoop) S S1 1 := Eval.push_eq hrl
  have hS1R : S1.stk Div.stR = bitsG (d :: r) ++ gR :: b0.stk Div.stR := by
    have h : S1.stk Div.stR = Glyph.bit d :: (bitsG r ++ [gR] ++ b0.stk Div.stR) := by
      simp [S1, hR]
    rw [h]; simp [bitsG]
  have hS1X : S1.stk Div.stX = [gX] ++ b0.stk Div.stX := by
    have h : S1.stk Div.stX = S.stk Div.stX :=
      upd_stk_of_ne hneXR (Glyph.bit d :: S.stk Div.stR)
    rw [h, hX]
  -- step 2: reverse the region onto the scratch stack `stX`
  have hT : ∀ g ∈ bitsG (d :: r), g ≠ gR := by
    intro g hg
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
    exact fun h => by cases h
  obtain ⟨S2, n2, h2, hn2, hS2R, hS2X, hfr2⟩ :=
    eval_mvRevOnto main Div.stR gR Div.stX Div.rgT (bitsG (d :: r)) (b0.stk Div.stR)
      ([gX] ++ b0.stk Div.stX) S1 hT hS1R hS1X hneRX
  -- step 3: drop the padding zero
  obtain ⟨S3, h3, hS3X, hfr3⟩ :=
    div_shiftR_pop main b0 d r L hr hl S2 (by rw [hS2X, List.append_assoc])
  -- steps 4, 5: reverse back onto `stR` and restore the marker of `stX`
  have hl_mem : ∀ g ∈ ((bitsG (r.take (L - 1))).reverse ++ [Glyph.bit d]), g ≠ gX := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · have h' : g ∈ ((r.take (L - 1)).reverse).map Glyph.bit := by
        simpa [bitsG, List.map_reverse] using h
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp h'
      exact fun hh => by cases hh
    · rw [List.mem_singleton] at h
      subst h
      exact fun hh => by cases hh
  have hS3R : S3.stk Div.stR = b0.stk Div.stR := by rw [hfr3 Div.stR hneRX, hS2R]
  obtain ⟨S4, n4, h4, hn4, hS4R, hS4X, hfr4⟩ :=
    div_shiftR_mvRev main b0 ((bitsG (r.take (L - 1))).reverse ++ [Glyph.bit d]) S3 hl_mem hS3X hS3R
  have hlrev : ((bitsG (r.take (L - 1))).reverse ++ [Glyph.bit d]).reverse =
      bitsG (d :: r.take (L - 1)) := by
    simp [bitsG]
  have hl_len : ((bitsG (r.take (L - 1))).reverse ++ [Glyph.bit d]).length ≤ L := by
    have h1len : ((bitsG (r.take (L - 1))).reverse ++ [Glyph.bit d]).length
        = (r.take (L - 1)).length + 1 := by simp [bitsG]
    have h2len : (r.take (L - 1)).length ≤ L - 1 := List.length_take_le (L - 1) r
    omega
  have hb_len : (bitsG (d :: r)).length ≤ L + 1 := by
    have hb : (bitsG (d :: r)).length = r.length + 1 := by simp [bitsG]
    omega
  refine ⟨S4, 1 + (n2 + (1 + n4)), ?_, ?_, ?_, ?_, ?_⟩
  · have h := Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4))
    simpa [Div.shiftR] using h
  · omega
  · rw [hS4R, hlrev]
  · exact hS4X
  · intro j hjR hjX
    calc S4.stk j = S3.stk j := hfr4 j hjR hjX
      _ = S2.stk j := hfr3 j hjX
      _ = S1.stk j := hfr2 j hjR hjX
      _ = S.stk j := upd_stk_of_ne hjR (Glyph.bit d :: S.stk Div.stR)

end Work.IntLib
