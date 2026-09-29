import Mathlib
import Submission.Work.Resample.paWords
import Submission.Work.Resample.paDefs
import Submission.Work.IntLib.Shift.Base

/-!
# The "tap" word of the `Ã` program: removing the marker under a single top value

`WordPe` programs start from a stack 0 of the shape `encs vs ++ paMark :: (encs rest ++ R0)`
(the marker `paMark` separates the data of the procedure from the honest suffix `rest`) and must
return the stack `encs out ++ (encs rest ++ R0)` with the marker *removed*.  This file provides the
elementary instance of that job: the value stack above the marker is a single value `arr`.

The program `paTapProg` parks the raw glyph block `arr.enc` above the marker on a scratch stack
(stack 1, which is restored to its original content at the end), pops the marker, and moves the
block back:

```
set 0 paMark ; push 1 0          -- sentinel paMark at the bottom of the scratch stack
drainPop 0 1 paMark 0 1          -- move arr.enc onto stack 1 (reversed), pop the marker
drain 1 0 paMark 2 3             -- move it back (reversing again)
pop 1 2                          -- drop the sentinel
```

The two `drain`s are `Work.IntLib.Shift.drain`, whose cost is `5 * (length + 1) + 2` and which is
exactly the intended tool: they move a region delimited by a marker `T` from one stack to another
and leave everything else untouched.  The total cost is `≤ 10 * vsz arr + 19 ≤ 20 * (vsz arr + 1)`.
The absence of `Glyph.mk` from the encoding of a value (`Work.Resample.noMark_enc`) guarantees that
the loop of `drain` never mistakes a data glyph for the marker.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Resample

open HvdH

/-- Raw-glyph "tap": remove the marker `paMark` sitting directly below the encoding of the single
top value of stack 0, using stack 1 as scratch. -/
def paTapProg : Cmd :=
  .seq (.seq (.set 0 paMark) (.push 1 0))
       (.seq (Work.IntLib.Shift.drainPop 0 1 paMark 0 1)
             (.seq (Work.IntLib.Shift.drain 1 0 paMark 2 3) (.pop 1 2)))

theorem paTapD :
    ∃ (prog : HvdH.Cmd) (Kc : ℕ), ∀ (main : HvdH.Cmd),
      Work.Resample.WordPe main prog
        (fun vs _ a => ∃ arr : HvdH.Val, vs = [arr] ∧ (∀ k : HvdH.Stk, k ≠ 0 → a k = []))
        (fun vs _ a out b => ∃ arr : HvdH.Val, vs = [arr] ∧ out = [arr] ∧
          (∀ k : HvdH.Stk, k ≠ 0 → b k = []))
        (fun vs _ _ => Kc * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1)) := by
  refine ⟨paTapProg, 20, ?_⟩
  intro main vs rest a hpre s R0 Bg h0 hk
  obtain ⟨arr, hvs, ha⟩ := hpre
  -- the two concrete facts about the initial state
  have h0a : s.stk 0 = arr.enc ++ paMark :: (encs rest ++ R0) := by
    rw [h0, hvs]
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
  have hs1 : s.stk 1 = Bg 1 := by
    have h := hk 1 (by decide)
    rw [ha 1 (by decide), Work.Kernel.encs_nil, List.nil_append] at h
    exact h
  -- phase 1: push the sentinel marker on the scratch stack 1
  let s1 : State := ⟨Function.update s.reg 0 paMark, Function.update s.stk 1 (paMark :: s.stk 1)⟩
  have hev1 : Work.IntLib.Shift.Ev main (.seq (.set 0 paMark) (.push 1 0)) s s1 2 := by
    have hset : Work.IntLib.Shift.Ev main (.set 0 paMark) s
        ⟨Function.update s.reg 0 paMark, s.stk⟩ 1 :=
      Work.IntLib.Shift.ev_set' main 0 paMark s.reg s.stk
    have hpush : Work.IntLib.Shift.Ev main (.push 1 0)
        ⟨Function.update s.reg 0 paMark, s.stk⟩ s1 1 := by
      have h := Work.IntLib.Shift.ev_push' main 1 0 (Function.update s.reg 0 paMark) s.stk
      simpa only [s1, Function.update_self] using h
    exact Work.IntLib.Shift.Ev.seq' hset hpush (by norm_num)
  have hX0 : s1.stk 0 = arr.enc ++ paMark :: (encs rest ++ R0) := by
    show Function.update s.stk 1 (paMark :: s.stk 1) 0 = _
    rw [Function.update_of_ne (by decide : (0 : Stk) ≠ 1)]
    exact h0a
  have hX1 : s1.stk 1 = paMark :: Bg 1 := by
    show Function.update s.stk 1 (paMark :: s.stk 1) 1 = _
    rw [Function.update_self, hs1]
  -- phase 2: move the block `arr.enc` onto stack 1 and drop the marker
  have hG : ∀ h ∈ arr.enc, h ≠ paMark := fun h hh hh' => paMark_ne_enc arr (hh' ▸ hh)
  obtain ⟨s2, n2, hev2, hn2, hs20, hs21, hfr2⟩ :=
    Work.IntLib.Shift.drainPop_ev main 0 1 paMark 0 1 (by decide) (by decide)
      arr.enc (encs rest ++ R0) (paMark :: Bg 1) s1.reg s1.stk hG hX0 hX1
  -- phase 3: move the block back onto stack 0 (reversing again)
  have hG' : ∀ h ∈ arr.enc.reverse, h ≠ paMark := by
    intro h hh hh'
    exact paMark_ne_enc arr (hh' ▸ (List.mem_reverse.mp hh))
  obtain ⟨s3, n3, hev3, hn3, _, hs31, hs30, hfr3⟩ :=
    Work.IntLib.Shift.drain_ev main 1 0 paMark 2 3 (by decide) (by decide)
      arr.enc.reverse (Bg 1) (encs rest ++ R0) s2.reg s2.stk hG' hs21 hs20
  -- phase 4: drop the sentinel
  let s4 : State := ⟨Function.update s3.reg 2 ((s3.stk 1).headD .eos),
    Function.update s3.stk 1 (s3.stk 1).tail⟩
  have hev4 : Work.IntLib.Shift.Ev main (.pop 1 2) s3 s4 1 := by
    have h := Work.IntLib.Shift.ev_pop' main 1 2 s3.reg s3.stk
    simpa only [s4] using h
  -- assemble the run
  have h34 : Work.IntLib.Shift.Ev main
      (.seq (Work.IntLib.Shift.drain 1 0 paMark 2 3) (.pop 1 2))
      s2 s4 (5 * (arr.enc.reverse.length + 1) + 2 + 1) :=
    Work.IntLib.Shift.Ev.seq' ⟨n3, hev3, hn3⟩ hev4 (by omega)
  have h24 : Work.IntLib.Shift.Ev main
      (.seq (Work.IntLib.Shift.drainPop 0 1 paMark 0 1)
            (.seq (Work.IntLib.Shift.drain 1 0 paMark 2 3) (.pop 1 2)))
      s1 s4 (5 * (arr.enc.length + 1) + 4 + (5 * (arr.enc.reverse.length + 1) + 2 + 1)) :=
    Work.IntLib.Shift.Ev.seq' ⟨n2, hev2, hn2⟩ h34 (by omega)
  have hP : Work.IntLib.Shift.Ev main paTapProg s s4
      (2 + (5 * (arr.enc.length + 1) + 4 + (5 * (arr.enc.reverse.length + 1) + 2 + 1))) := by
    show Work.IntLib.Shift.Ev main
      (.seq (.seq (.set 0 paMark) (.push 1 0))
        (.seq (Work.IntLib.Shift.drainPop 0 1 paMark 0 1)
          (.seq (Work.IntLib.Shift.drain 1 0 paMark 2 3) (.pop 1 2)))) s s4 _
    exact Work.IntLib.Shift.Ev.seq' hev1 h24 (by omega)
  obtain ⟨n, hev, hn⟩ := hP
  refine ⟨[arr], (fun _ => []), s4, n, ⟨arr, hvs, rfl, fun k _ => rfl⟩, hev, ?_, ?_, ?_⟩
  · -- cost bound
    rw [hvs]
    have hn' := hn
    rw [List.length_reverse] at hn'
    show n ≤ 20 * (arr.enc.length + 1)
    omega
  · -- the value stack
    show s4.stk 0 = encs [arr] ++ (encs rest ++ R0)
    have hs40 : s4.stk 0 = s3.stk 0 :=
      Function.update_of_ne (by decide : (0 : Stk) ≠ 1) (s3.stk 1).tail s3.stk
    rw [hs40, hs30, List.reverse_reverse]
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
  · -- all other stacks restored
    intro k hk0
    show s4.stk k = encs ([] : List Val) ++ Bg k
    rw [Work.Kernel.encs_nil, List.nil_append]
    by_cases hk1 : k = 1
    · subst hk1
      have hs41 : s4.stk 1 = (s3.stk 1).tail := Function.update_self 1 (s3.stk 1).tail s3.stk
      rw [hs41, hs31]
      rfl
    · have hs4k : s4.stk k = s3.stk k :=
        Function.update_of_ne hk1 (s3.stk 1).tail s3.stk
      rw [hs4k, hfr3 k hk1 hk0, hfr2 k hk0 hk1]
      show Function.update s.stk 1 (paMark :: s.stk 1) k = Bg k
      rw [Function.update_of_ne hk1, hk k hk0, ha k hk0]
      rfl

end Work.Resample
