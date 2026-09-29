import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.eval_subBitProg
import Submission.Work.IntLib.rippleArith

/-!
# `div_rippleProgBR_eval`: the ripple subtraction of the long-division core

`Div.rippleProg stB stR gB gR` consumes the bit region `bitsG A` of stack `stB` (least significant
bit on top) and, for each bit `A i`, ripples through the corresponding bit `B i` of the region
`bitsG B` of stack `stR` (`subBitProg`), accumulating the reversed divisor bits on `stC`, the
reversed dividend bits on `stD` and the reversed result bits on `stS`, with the borrow carried in
`rgC`.  At the end the two input regions and their markers are gone, the accumulated regions sit
above their markers, and the final borrow is `(subRippleBits A B false).1`.

The proof is a loop unrolling.  `ripSt` (in `Submission/Work/IntLib/rippleArith.lean`) is the state
after `i` completed steps; `ripSt_step` advances it by one `consumeStep` (cost `≤ 13`),
`ripSt_step_end` handles the terminal `consumeStep` that pops the frame marker `gB` (cost `4`), and
`ripSt_loop` unrolls the loop with `eval_loop_iterate_le`.  The remaining lines run the two
preparatory `set`s, the two final `pop`s and the trailing `skip`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib

open HvdH

/-! ## The take form of `bitsG` -/

/-- Taking `i + 1` glyphs of `bitsG A` appends the `i`-th bit, in the (`List.take`-normal) form in
which `simp` presents it. -/
theorem take_bitsG_rev_succ (A : List Bool) (i : ℕ) (hi : i < A.length) :
    (List.take (i + 1) (bitsG A)).reverse =
      Glyph.bit (A.getD i false) :: (List.take i (bitsG A)).reverse := by
  rw [← List.map_take, ← List.map_take, bitsG_take_rev_succ A i hi]

/-! ## The initial state of the loop -/

/-- After the two preparatory `set`s (`rgC := false`, `rLoop := eos`) the loop starts from the state
family at `i = 0`. -/
theorem ripSt_zero (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (hB : S.stk Div.stB = bitsG A ++ [gB] ++ blB)
    (hR : S.stk Div.stR = bitsG B ++ [gR] ++ blR)
    (hC : S.stk Div.stC = [gC] ++ blC)
    (hD : S.stk Div.stD = [gD] ++ blD)
    (hS5 : S.stk Div.stS = [gS] ++ blS) :
    ripSt S blB blR blC blD blS A B 0 =
      (S.updReg Div.rgC (Glyph.bit false)).updReg rLoop Glyph.eos := by
  have hsr : subRippleBits (A.take 0) (B.take 0) false = (false, ([] : List Bool)) := rfl
  refine State.ext_mk ?_ ?_
  · funext r
    fin_cases r <;>
      simp (config := { decide := true }) [ripSt, State.updReg, State.updStk,
        Function.update_apply, subRippleBits, hsr]
  · funext j
    fin_cases j <;>
      simp (config := { decide := true }) [ripSt, State.updReg, State.updStk,
        Function.update_apply, subRippleBits, hsr, hB, hR, hC, hD, hS5]

/-! ## One iteration of the ripple loop -/

/-- One iteration of the ripple loop: `consumeStep` pops the `i`-th dividend bit from `stB`, the
handler pops the `i`-th divisor bit from `stR` and advances `stC`, `stD`, `stS` and `rgC`, and the
loop register is set back to `eos`.  Cost `≤ 13`. -/
theorem ripSt_step (main : Cmd) (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) (hAB : A.length = B.length) (hi : i < A.length) :
    ∃ n, Eval main (consumeStep Div.stB gB rLoop (Div.rippleBody Div.stR))
        (ripSt S blB blR blC blD blS A B i) (ripSt S blB blR blC blD blS A B (i + 1)) n ∧
      n ≤ 13 := by
  have hBlt : i < B.length := by omega
  have hdropA := bitsG_drop_succ A i hi
  have hdropB := bitsG_drop_succ B i hBlt
  have htakeB := take_bitsG_rev_succ B i hBlt
  have htakeA := take_bitsG_rev_succ A i hi
  have hrip := subRippleBits_take_succ A B hAB i hi
  set s1 := ripSt S blB blR blC blD blS A B i with hs1
  set s2 := State.tPop s1 Div.stB rLoop with hs2
  set r1 := State.tPop s2 Div.stR Div.rgB with hr1
  set r2 := State.tPush r1 Div.stC Div.rgB with hr2
  set r3 := State.tPush r2 Div.stD rLoop with hr3
  set r4 := (r3.updReg Div.rgS (Glyph.bit (subBitVal (A.getD i false) (B.getD i false)
              (subRippleBits (A.take i) (B.take i) false).1))).updReg Div.rgC
              (Glyph.bit (subBorrow (A.getD i false) (B.getD i false)
              (subRippleBits (A.take i) (B.take i) false).1)) with hr4
  set r5 := State.tPush r4 Div.stS Div.rgS with hr5
  set s3 := State.tSet r5 rLoop Glyph.eos with hs3
  have e1 : Eval main (.pop Div.stB rLoop) s1 s2 1 := by rw [hs2]; exact Eval.pop _ _ _
  have e2 : Eval main (.pop Div.stR Div.rgB) s2 r1 1 := by rw [hr1]; exact Eval.pop _ _ _
  have e3 : Eval main (.push Div.stC Div.rgB) r1 r2 1 := by rw [hr2]; exact Eval.push _ _ _
  have e4 : Eval main (.push Div.stD rLoop) r2 r3 1 := by rw [hr3]; exact Eval.push _ _ _
  have h3reg : r3.reg rLoop = Glyph.bit (A.getD i false) ∧
      r3.reg Div.rgB = Glyph.bit (B.getD i false) ∧
      r3.reg Div.rgC = Glyph.bit ((subRippleBits (A.take i) (B.take i) false).1) := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) [hr3, hr2, hr1, hs2, hs1, State.tPop, State.tPush,
        State.updStk, State.updReg, Function.update_apply, ripSt, hdropA, hdropB]
  have e5 : Eval main (subBitProg rLoop Div.rgB Div.rgC Div.rgS) r3 r4 5 := by
    rw [hr4]
    exact eval_subBitProg main rLoop Div.rgB Div.rgC Div.rgS r3 (A.getD i false)
      (B.getD i false) ((subRippleBits (A.take i) (B.take i) false).1)
      h3reg.1 h3reg.2.1 h3reg.2.2
  have e6 : Eval main (.push Div.stS Div.rgS) r4 r5 1 := by rw [hr5]; exact Eval.push _ _ _
  have e7 : Eval main (.skip) r5 r5 1 := Eval.skip r5
  have ehand : Eval main (Div.rippleBody Div.stR) s2 r5 10 := by
    have h := Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 e7))))
    simpa [Div.rippleBody] using h
  have hreg2 : s2.reg rLoop = Glyph.bit (A.getD i false) := by
    simp (config := { decide := true }) [hs2, hs1, State.tPop, State.updStk, State.updReg,
      Function.update_apply, ripSt, hdropA]
  have hne2 : s2.reg rLoop ≠ gB := by
    rw [hreg2]; intro h; cases h
  have e8 : Eval main (.set rLoop Glyph.eos) r5 s3 1 := by rw [hs3]; exact Eval.set _ _ _
  have eite : Eval main (.ite rLoop gB (.seq (.push Div.stB rLoop) (.set rLoop (Glyph.mk 0)))
      (.seq (Div.rippleBody Div.stR) (.set rLoop Glyph.eos))) s2 s3 12 :=
    Eval.iteF hne2 (Eval.seq ehand e8)
  have ebody : Eval main (consumeStep Div.stB gB rLoop (Div.rippleBody Div.stR)) s1 s3 13 := by
    have h := Eval.seq e1 eite
    simpa [consumeStep] using h
  have hs3eq : s3 = ripSt S blB blR blC blD blS A B (i + 1) := by
    refine State.ext_mk ?_ ?_
    · funext r
      fin_cases r <;>
        simp (config := { decide := true }) [hs3, hr5, hr4, hr3, hr2, hr1, hs2, hs1, State.tPop,
          State.tPush, State.tSet, State.updStk, State.updReg, Function.update_apply, ripSt,
          hdropA, hdropB, htakeA, htakeB, hrip, subRippleBits]
    · funext j
      fin_cases j <;>
        simp (config := { decide := true }) [hs3, hr5, hr4, hr3, hr2, hr1, hs2, hs1, State.tPop,
          State.tPush, State.tSet, State.updStk, State.updReg, Function.update_apply, ripSt,
          hdropA, hdropB, htakeA, htakeB, hrip, subRippleBits]
  refine ⟨13, ?_, le_refl 13⟩
  rw [← hs3eq]
  exact ebody

/-! ## The terminal iteration -/

/-- The terminal iteration of the ripple loop: the head of `stB` is the frame marker `gB`, so the
`consumeStep` pushes it back and leaves `mk 0` in the loop register, which stops the loop.  Cost
`4`. -/
theorem ripSt_step_end (main : Cmd) (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) :
    Eval main (consumeStep Div.stB gB rLoop (Div.rippleBody Div.stR))
      (ripSt S blB blR blC blD blS A B A.length)
      ((ripSt S blB blR blC blD blS A B A.length).updReg rLoop (Glyph.mk 0)) 4 := by
  set s1 := ripSt S blB blR blC blD blS A B A.length with hs1
  have hs1B : s1.stk Div.stB = [gB] ++ blB := by
    rw [hs1, ripSt_stB, bitsG_drop_length]
    rfl
  set s2 := State.tPop s1 Div.stB rLoop with hs2
  set s3 := State.tPush s2 Div.stB rLoop with hs3
  set s4 := State.tSet s3 rLoop (Glyph.mk 0) with hs4
  have e1 : Eval main (.pop Div.stB rLoop) s1 s2 1 := by rw [hs2]; exact Eval.pop _ _ _
  have hreg2 : s2.reg rLoop = gB := by
    simp (config := { decide := true }) [hs2, hs1B, State.tPop, State.updStk, State.updReg,
      Function.update_apply]
  have e2 : Eval main (.push Div.stB rLoop) s2 s3 1 := by rw [hs3]; exact Eval.push _ _ _
  have e3 : Eval main (.set rLoop (Glyph.mk 0)) s3 s4 1 := by rw [hs4]; exact Eval.set _ _ _
  have eite : Eval main (.ite rLoop gB (.seq (.push Div.stB rLoop) (.set rLoop (Glyph.mk 0)))
      (.seq (Div.rippleBody Div.stR) (.set rLoop Glyph.eos))) s2 s4 3 :=
    Eval.iteT hreg2 (Eval.seq e2 e3)
  have hbody : Eval main (consumeStep Div.stB gB rLoop (Div.rippleBody Div.stR)) s1 s4 4 := by
    have h := Eval.seq e1 eite
    simpa [consumeStep] using h
  have hs4eq : s4 = (ripSt S blB blR blC blD blS A B A.length).updReg rLoop (Glyph.mk 0) := by
    refine State.ext_mk ?_ ?_
    · funext r
      fin_cases r <;>
        simp (config := { decide := true }) [hs4, hs3, hs2, hs1, hs1B, State.tSet, State.tPush,
          State.tPop, State.updStk, State.updReg, Function.update_apply, ripSt, subRippleBits,
          bitsG_drop_length]
    · funext j
      fin_cases j <;>
        simp (config := { decide := true }) [hs4, hs3, hs2, hs1, hs1B, State.tSet, State.tPush,
          State.tPop, State.updStk, State.updReg, Function.update_apply, ripSt, subRippleBits,
          bitsG_drop_length]
  have hgoal : Eval main (consumeStep Div.stB gB rLoop (Div.rippleBody Div.stR)) s1
      ((ripSt S blB blR blC blD blS A B A.length).updReg rLoop (Glyph.mk 0)) 4 := by
    rw [← hs4eq]
    exact hbody
  exact hgoal

/-! ## Unrolling the loop -/

/-- The whole `consumeLoop`: from the state family at `i = 0` to the terminal state, at a cost
linear in the length of the consumed region. -/
theorem ripSt_loop (main : Cmd) (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (hAB : A.length = B.length) :
    ∃ m, Eval main (consumeLoop Div.stB gB rLoop (Div.rippleBody Div.stR))
        (ripSt S blB blR blC blD blS A B 0)
        ((ripSt S blB blR blC blD blS A B A.length).updReg rLoop (Glyph.mk 0)) m ∧
      m ≤ (A.length + 1) * 14 + 1 := by
  have hstep : ∀ i < A.length + 1, (ripFam S blB blR blC blD blS A B i).reg rLoop = Glyph.eos ∧
      ∃ m, Eval main (consumeStep Div.stB gB rLoop (Div.rippleBody Div.stR))
        (ripFam S blB blR blC blD blS A B i) (ripFam S blB blR blC blD blS A B (i + 1)) m ∧
        m ≤ 13 := by
    intro i hi
    by_cases hlt : i < A.length
    · have hfi : ripFam S blB blR blC blD blS A B i = ripSt S blB blR blC blD blS A B i :=
        ripFam_of_le S blB blR blC blD blS A B i (by omega)
      have hfi1 : ripFam S blB blR blC blD blS A B (i + 1) =
          ripSt S blB blR blC blD blS A B (i + 1) :=
        ripFam_of_le S blB blR blC blD blS A B (i + 1) (by omega)
      rw [hfi, hfi1]
      obtain ⟨n, hev, hn⟩ := ripSt_step main S blB blR blC blD blS A B i hAB hlt
      exact ⟨by simp, n, hev, hn⟩
    · have hiN : i = A.length := by omega
      subst hiN
      have hfi : ripFam S blB blR blC blD blS A B A.length =
          ripSt S blB blR blC blD blS A B A.length :=
        ripFam_of_le S blB blR blC blD blS A B A.length (le_refl _)
      have hfi1 : ripFam S blB blR blC blD blS A B (A.length + 1) =
          (ripSt S blB blR blC blD blS A B A.length).updReg rLoop (Glyph.mk 0) :=
        ripFam_of_gt S blB blR blC blD blS A B (A.length + 1) (by omega)
      rw [hfi, hfi1]
      exact ⟨by simp, 4, ripSt_step_end main S blB blR blC blD blS A B, by norm_num⟩
  have hstop : (ripFam S blB blR blC blD blS A B (A.length + 1)).reg rLoop ≠ Glyph.eos := by
    rw [ripFam_of_gt S blB blR blC blD blS A B (A.length + 1) (by omega)]
    simp
  obtain ⟨m, hev, hm⟩ := eval_loop_iterate_le main rLoop Glyph.eos
    (consumeStep Div.stB gB rLoop (Div.rippleBody Div.stR)) 13 (A.length + 1)
    (ripFam S blB blR blC blD blS A B) hstep hstop
  refine ⟨m, ?_, hm⟩
  rw [← ripFam_of_le S blB blR blC blD blS A B 0 (Nat.zero_le _),
    ← ripFam_of_gt S blB blR blC blD blS A B (A.length + 1) (by omega)]
  exact hev

/-! ## The whole ripple program -/

/-- `Div.rippleProg stB stR gB gR` on the state described by the five hypotheses: it removes both
input regions, accumulates the reversed divisor/dividend bits and the result bits, and restores
every other stack. -/
theorem rippleProgBR_eval_gen (main : Cmd) (S : State) (blB blR blC blD blS : List Glyph)
    (A B : List Bool) (hAB : A.length = B.length)
    (hB : S.stk Div.stB = bitsG A ++ [gB] ++ blB)
    (hR : S.stk Div.stR = bitsG B ++ [gR] ++ blR)
    (hC : S.stk Div.stC = [gC] ++ blC)
    (hD : S.stk Div.stD = [gD] ++ blD)
    (hS5 : S.stk Div.stS = [gS] ++ blS) :
    ∃ s' m, Eval main (Div.rippleProg Div.stB Div.stR gB gR) S s' m ∧
      m ≤ 14 * (A.length + 2) + 6 ∧
      s'.stk Div.stB = blB ∧ s'.stk Div.stR = blR ∧
      s'.stk Div.stS = (bitsG ((subRippleBits A B false).2)).reverse ++ [gS] ++ blS ∧
      s'.stk Div.stC = (bitsG B).reverse ++ [gC] ++ blC ∧
      s'.stk Div.stD = (bitsG A).reverse ++ [gD] ++ blD ∧
      (∀ j : Stk, j ≠ Div.stB → j ≠ Div.stR → j ≠ Div.stS → j ≠ Div.stC → j ≠ Div.stD →
        s'.stk j = S.stk j) := by
  have hda : (bitsG A).drop A.length = ([] : List Glyph) := bitsG_drop_length A
  have hdb : (bitsG B).drop A.length = ([] : List Glyph) := by rw [hAB, bitsG_drop_length]
  have hta : A.take A.length = A := List.take_length
  have htb : B.take A.length = B := by rw [hAB, List.take_length]
  set S2 := (S.updReg Div.rgC (Glyph.bit false)).updReg rLoop Glyph.eos with hS2
  have hS2eq : ripSt S blB blR blC blD blS A B 0 = S2 :=
    ripSt_zero S blB blR blC blD blS A B hB hR hC hD hS5
  obtain ⟨ml, hevl, hml⟩ := ripSt_loop main S blB blR blC blD blS A B hAB
  set E := (ripSt S blB blR blC blD blS A B A.length).updReg rLoop (Glyph.mk 0) with hE
  set T1 := State.tPop E Div.stB rLoop with hT1
  set T2 := State.tPop T1 Div.stR Div.rgB with hT2
  have hEB : E.stk Div.stB = [gB] ++ blB := by
    rw [hE, State.updReg_stk, ripSt_stB, hda]
    rfl
  have hER : E.stk Div.stR = [gR] ++ blR := by
    rw [hE, State.updReg_stk, ripSt_stR, hdb]
    rfl
  have hEC : E.stk Div.stC = (bitsG B).reverse ++ [gC] ++ blC := by
    rw [hE, State.updReg_stk, ripSt_stC, htb]
  have hED : E.stk Div.stD = (bitsG A).reverse ++ [gD] ++ blD := by
    rw [hE, State.updReg_stk, ripSt_stD, hta]
  have hES : E.stk Div.stS = (bitsG ((subRippleBits A B false).2)).reverse ++ [gS] ++ blS := by
    rw [hE, State.updReg_stk, ripSt_stS, hta, htb]
  have e1 : Eval main (.set Div.rgC (Glyph.bit false)) S
      (S.updReg Div.rgC (Glyph.bit false)) 1 := Eval.set _ _ _
  have e2 : Eval main (.set rLoop Glyph.eos) (S.updReg Div.rgC (Glyph.bit false)) S2 1 := by
    rw [hS2]; exact Eval.set _ _ _
  have e3 : Eval main (consumeLoop Div.stB gB rLoop (Div.rippleBody Div.stR)) S2 E ml := by
    rw [← hS2eq]
    exact hevl
  have e4 : Eval main (.pop Div.stB rLoop) E T1 1 := by rw [hT1]; exact Eval.pop _ _ _
  have e5 : Eval main (.pop Div.stR Div.rgB) T1 T2 1 := by rw [hT2]; exact Eval.pop _ _ _
  have e6 : Eval main (.skip) T2 T2 1 := Eval.skip T2
  have hwhole : Eval main (Div.rippleProg Div.stB Div.stR gB gR) S T2
      (1 + ((1 + ml) + (1 + (1 + 1)))) := by
    have h := Eval.seq e1 (Eval.seq (Eval.seq e2 e3) (Eval.seq e4 (Eval.seq e5 e6)))
    simpa [Div.rippleProg, Div.seqs, consume] using h
  have hTB : T2.stk Div.stB = blB := by
    rw [hT2, hT1, Div.tPop_stk_ne T1 Div.stR Div.rgB Div.stB (by decide),
      Div.tPop_stk_same E Div.stB rLoop, hEB]
    simp
  have hTR : T2.stk Div.stR = blR := by
    rw [hT2, Div.tPop_stk_same T1 Div.stR Div.rgB, hT1,
      Div.tPop_stk_ne E Div.stB rLoop Div.stR (by decide), hER]
    simp
  have hTS : T2.stk Div.stS = (bitsG ((subRippleBits A B false).2)).reverse ++ [gS] ++ blS := by
    rw [hT2, Div.tPop_stk_ne T1 Div.stR Div.rgB Div.stS (by decide), hT1,
      Div.tPop_stk_ne E Div.stB rLoop Div.stS (by decide), hES]
  have hTC : T2.stk Div.stC = (bitsG B).reverse ++ [gC] ++ blC := by
    rw [hT2, Div.tPop_stk_ne T1 Div.stR Div.rgB Div.stC (by decide), hT1,
      Div.tPop_stk_ne E Div.stB rLoop Div.stC (by decide), hEC]
  have hTD : T2.stk Div.stD = (bitsG A).reverse ++ [gD] ++ blD := by
    rw [hT2, Div.tPop_stk_ne T1 Div.stR Div.rgB Div.stD (by decide), hT1,
      Div.tPop_stk_ne E Div.stB rLoop Div.stD (by decide), hED]
  have hfr : ∀ j : Stk, j ≠ Div.stB → j ≠ Div.stR → j ≠ Div.stS → j ≠ Div.stC → j ≠ Div.stD →
      T2.stk j = S.stk j := by
    intro j h1 h2 h3 h4 h5
    have hx : T2.stk j = E.stk j := by
      rw [hT2, Div.tPop_stk_ne T1 Div.stR Div.rgB j h2, hT1,
        Div.tPop_stk_ne E Div.stB rLoop j h1]
    rw [hx, hE, State.updReg_stk]
    exact ripSt_stk_other S blB blR blC blD blS A B A.length j h1 h2 h4 h5 h3
  exact ⟨T2, 1 + ((1 + ml) + (1 + (1 + 1))), hwhole, by omega, hTB, hTR, hTS, hTC, hTD, hfr⟩

/-! ## The requested lemma -/

theorem div_rippleProgBR_eval (main : HvdH.Cmd) (b0 : HvdH.State) (Z : List HvdH.Glyph)
    (X Y : List Bool) (hXY : X.length = Y.length) :
    ∃ s' n, HvdH.Eval main
        (Work.IntLib.Div.rippleProg Work.IntLib.Div.stB Work.IntLib.Div.stR
          Work.IntLib.gB Work.IntLib.gR)
        (Work.IntLib.Div.gSt b0 Z (b0.stk Work.IntLib.Div.stP)
          (Work.IntLib.bitsG X ++ [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB)
          (Work.IntLib.bitsG Y ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR)
          (b0.stk Work.IntLib.Div.stQ)
          ([Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS)
          ([Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC)
          ([Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD)
          (b0.stk Work.IntLib.Div.stX) (b0.stk Work.IntLib.Div.stY)) s' n ∧
      n ≤ 14 * (X.length + 2) + 6 ∧
      s'.stk Work.IntLib.Div.stB = b0.stk Work.IntLib.Div.stB ∧
      s'.stk Work.IntLib.Div.stR = b0.stk Work.IntLib.Div.stR ∧
      s'.stk Work.IntLib.Div.stS = Work.IntLib.bitsG (Work.IntLib.subRippleBits X Y false).2.reverse ++
        [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS ∧
      s'.stk Work.IntLib.Div.stC = Work.IntLib.bitsG Y.reverse ++ [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC ∧
      s'.stk Work.IntLib.Div.stD = Work.IntLib.bitsG X.reverse ++ [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD ∧
      s'.stk 0 = Z ∧ s'.stk Work.IntLib.Div.stP = b0.stk Work.IntLib.Div.stP ∧
      s'.stk Work.IntLib.Div.stQ = b0.stk Work.IntLib.Div.stQ ∧
      s'.stk Work.IntLib.Div.stX = b0.stk Work.IntLib.Div.stX ∧
      s'.stk Work.IntLib.Div.stY = b0.stk Work.IntLib.Div.stY := by
  obtain ⟨s', m, hev, hm, hB', hR', hS', hC', hD', hfr⟩ :=
    rippleProgBR_eval_gen main
      (Div.gSt b0 Z (b0.stk Div.stP) (bitsG X ++ [gB] ++ b0.stk Div.stB)
        (bitsG Y ++ [gR] ++ b0.stk Div.stR) (b0.stk Div.stQ) ([gS] ++ b0.stk Div.stS)
        ([gC] ++ b0.stk Div.stC) ([gD] ++ b0.stk Div.stD) (b0.stk Div.stX) (b0.stk Div.stY))
      (b0.stk Div.stB) (b0.stk Div.stR) (b0.stk Div.stC) (b0.stk Div.stD) (b0.stk Div.stS)
      X Y hXY (by simp) (by simp) (by simp) (by simp) (by simp)
  refine ⟨s', m, hev, hm, hB', hR', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS', ← List.map_reverse]
  · rw [hC', ← List.map_reverse]
  · rw [hD', ← List.map_reverse]
  · simpa using hfr 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  · simpa using hfr Div.stP (by decide) (by decide) (by decide) (by decide) (by decide)
  · simpa using hfr Div.stQ (by decide) (by decide) (by decide) (by decide) (by decide)
  · simpa using hfr Div.stX (by decide) (by decide) (by decide) (by decide) (by decide)
  · simpa using hfr Div.stY (by decide) (by decide) (by decide) (by decide) (by decide)

end Work.IntLib
