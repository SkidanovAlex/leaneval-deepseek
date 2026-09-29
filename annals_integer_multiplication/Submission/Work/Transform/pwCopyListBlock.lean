import Mathlib
import Submission.Work.Transform.pwBase

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform

open HvdH
open Work.Kernel

/-!
# Non-destructive copy of a list block

The target lemma `Work.Transform.pwCopyListBlock` copies the encoding `(ofList xs).enc` of a list
`xs` of integer values from stack `src` to stack `dst` (above a fresh `Pw.gM` marker), restoring
`src` and the scratch stack `tmp`.

The proof is a single `Eval` chain over eight program steps:

1. push a scratch frame marker `Pw.gM` on `tmp`;
2. `Pw.tLoop src Glyph.nil tmp rB` moves everything above the *terminal* `nil` of the block onto
   `tmp`, reversed, and leaves the `nil` on top of `src`;
3. `pop src rA` pops that `nil` (`reg rA` now holds `Glyph.nil`);
4. push `Pw.gM` on `dst`;
5. re-push the `nil` on `src`;
6. re-push the `nil` on `dst`;
7. `Pw.tLoop2 tmp Pw.gM src dst rB` scans `tmp` down to its marker, restoring `src` and copying the
   block body, in the right orientation, onto both `src` and `dst`;
8. `pop tmp rA` removes the scratch marker from `tmp`.

The only arithmetic ingredient is that the elements of `xs` are integer values, so that the trailing
`nil` of `(ofList xs).enc` is its only `nil` glyph (`pw_enc_ofList_body` below).
-/

/-! ## The `ofList` encoding as a body plus a `nil` -/

/-- Sign glyph of an integer, as used by `Val.enc`. -/
def pwSg (z : ℤ) : Glyph := if z < 0 then Glyph.neg else Glyph.pos

/-- `Val.enc` of an integer, in terms of `pwSg`. -/
theorem pw_enc_int (z : ℤ) :
    (Val.int z).enc = pwSg z :: ((Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend]) :=
  rfl

theorem pwSg_ne_nil (z : ℤ) : pwSg z ≠ Glyph.nil := by
  unfold pwSg; split <;> decide

theorem pwSg_ne_gM (z : ℤ) : pwSg z ≠ Pw.gM := by
  unfold pwSg Pw.gM; split <;> decide

/-- The encoding of an integer value contains no `nil` glyph. -/
theorem pw_int_enc_ne_nil (z : ℤ) : ∀ g ∈ (Val.int z).enc, g ≠ Glyph.nil := by
  intro g hg
  rw [pw_enc_int] at hg
  rcases List.mem_cons.mp hg with rfl | hg'
  · exact pwSg_ne_nil z
  rcases List.mem_append.mp hg' with h1 | h2
  · obtain ⟨b, -, hb⟩ := List.mem_map.mp h1
    rw [← hb]; exact fun h => nomatch h
  · rw [List.mem_singleton] at h2
    rw [h2]; exact fun h => nomatch h

/-- The encoding of an integer value contains no `Pw.gM` glyph. -/
theorem pw_int_enc_ne_gM (z : ℤ) : ∀ g ∈ (Val.int z).enc, g ≠ Pw.gM := by
  intro g hg
  rw [pw_enc_int] at hg
  rcases List.mem_cons.mp hg with rfl | hg'
  · exact pwSg_ne_gM z
  rcases List.mem_append.mp hg' with h1 | h2
  · obtain ⟨b, -, hb⟩ := List.mem_map.mp h1
    rw [← hb]; exact fun h => nomatch h
  · rw [List.mem_singleton] at h2
    rw [h2]; exact fun h => nomatch h

theorem pw_ofList_cons (a : Val) (as : List Val) : ofList (a :: as) = Val.cons a (ofList as) := rfl

theorem pw_cons_enc (a b : Val) : (Val.cons a b).enc = Glyph.cons :: (a.enc ++ b.enc) := rfl

/-- For a list `xs` of integer values, `(ofList xs).enc` is a `body` followed by the single terminal
`nil`; the body contains neither `nil` nor `Pw.gM`. -/
theorem pw_enc_ofList_body (xs : List Val) (h : ∀ x ∈ xs, ∃ z : ℤ, x = Val.int z) :
    ∃ body : List Glyph, (ofList xs).enc = body ++ [Glyph.nil] ∧
      (∀ g ∈ body, g ≠ Glyph.nil) ∧ (∀ g ∈ body, g ≠ Pw.gM) := by
  induction xs with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a as ih =>
    obtain ⟨z, rfl⟩ := h a (by simp)
    obtain ⟨body, hbody, hnil, hgM⟩ := ih (fun x hx => h x (by simp [hx]))
    refine ⟨Glyph.cons :: ((Val.int z).enc ++ body), ?_, ?_, ?_⟩
    · rw [pw_ofList_cons, pw_cons_enc, hbody]
      simp [List.append_assoc]
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact fun h => nomatch h
      rcases List.mem_append.mp hg' with h1 | h2
      · exact pw_int_enc_ne_nil z g h1
      · exact hnil g h2
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact fun h => nomatch h
      rcases List.mem_append.mp hg' with h1 | h2
      · exact pw_int_enc_ne_gM z g h1
      · exact hgM g h2

theorem pw_nil_ne_eos : Glyph.nil ≠ Glyph.eos := by decide

/-! ## The copy word -/

/-- Program of `pwCopyListBlock`: the eight steps listed at the top of the file, with `rA = 0`
(holding the terminal `nil`) and `rB = 1` (loop register of `tLoop`/`tLoop2`). -/
def copyBlockProg (src dst tmp : Stk) (rA rB : Reg) : Cmd :=
  .seq (.set rA Pw.gM) (.seq (.push tmp rA)
   (.seq (Pw.tLoop src Glyph.nil tmp rB)
    (.seq (.pop src rA)
     (.seq (.set rB Pw.gM) (.seq (.push dst rB)
      (.seq (.push src rA) (.seq (.push dst rA)
       (.seq (Pw.tLoop2 tmp Pw.gM src dst rB) (.pop tmp rA)))))))))

/-- Non-destructive copy of a list block: the encoding of `ofList xs` (all of whose elements are
integer values, so that the only `nil` glyph in the block is the terminal one) sits above `rest` on
stack `src` (so `src` is NOT bounded by a frame marker); the program copies it, in the same
orientation, to stack `dst`, above a fresh `gM` marker that it pushes
(`gM := Work.Transform.Pw.gM`; `dst` becomes `(ofList xs).enc ++ gM :: old dst`), leaving `src` and
the scratch stack `tmp` exactly as they were.

Intended implementation: `Pw.tLoop src Glyph.nil tmp r` (moves everything above the `nil` to `tmp`,
reversed, and leaves the `nil` on top of `src`), `pop src r` (the `nil`), then push `gM` on `dst` and
push the `nil` on both `src` and `dst`, then `Pw.tLoop2 tmp gM src dst r` — this restores `src` and
simultaneously copies the block, in the right orientation, onto `dst`; finally pop the `gM` from
`tmp`.  Note that `tLoop2`'s `below` argument must be the stack content under the `gM` on `tmp`
(namely `s.stk tmp`), and that `src` must first get its `nil` back (push it before the `tLoop2`).
The cost is linear in `(ofList xs).enc.length`. -/
theorem pwCopyListBlock (src dst tmp : HvdH.Stk) :
    src ≠ dst → tmp ≠ src → tmp ≠ dst →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (xs : List HvdH.Val) (rest : List HvdH.Glyph) (s : HvdH.State),
      (∀ x ∈ xs, ∃ z : ℤ, x = HvdH.Val.int z) →
      s.stk src = (HvdH.ofList xs).enc ++ rest →
      ∃ s' n, HvdH.Eval main prog s s' n ∧ n ≤ K * ((HvdH.ofList xs).enc.length + 1) ∧
        s'.stk src = (HvdH.ofList xs).enc ++ rest ∧
        s'.stk dst = (HvdH.ofList xs).enc ++ Work.Transform.Pw.gM :: s.stk dst ∧
        s'.stk tmp = s.stk tmp ∧
        (∀ j : HvdH.Stk, j ≠ src → j ≠ dst → j ≠ tmp → s'.stk j = s.stk j) := by
  intro h1 h2 h3
  have h1' : dst ≠ src := h1.symm
  have h2' : src ≠ tmp := h2.symm
  have h3' : dst ≠ tmp := h3.symm
  refine ⟨copyBlockProg src dst tmp 0 1, 21, ?_⟩
  intro main xs rest s hxs hstk
  obtain ⟨body, hbody, hnil, hgM⟩ := pw_enc_ofList_body xs hxs
  have hsrc : s.stk src = body ++ Glyph.nil :: rest := by
    rw [hstk, hbody, List.append_assoc, List.singleton_append]
  -- step 1: push the scratch frame marker `gM` on `tmp`
  set s1 : State := State.tPush (State.tSet s 0 Pw.gM) tmp 0 with hs1
  have e1a : Eval main (.set (0 : Reg) Pw.gM) s (State.tSet s 0 Pw.gM) 1 :=
    eval_set main 0 Pw.gM s
  have e1b : Eval main (.push tmp 0) (State.tSet s 0 Pw.gM) s1 1 := by
    rw [hs1]; exact eval_push main tmp 0 (State.tSet s 0 Pw.gM)
  have h1src : s1.stk src = body ++ Glyph.nil :: rest := by
    rw [hs1, Pw.tPush_stk, if_neg h2', Pw.tSet_stk, hsrc]
  have h1tmp : s1.stk tmp = Pw.gM :: s.stk tmp := by
    rw [hs1, Pw.tPush_stk, if_pos rfl, Pw.tSet_stk, Pw.tSet_reg, if_pos rfl]
  have h1o : ∀ j, j ≠ tmp → s1.stk j = s.stk j := by
    intro j hj
    rw [hs1, Pw.tPush_stk, if_neg hj, Pw.tSet_stk]
  -- step 2: move the block body to `tmp` (reversed), leaving the terminal `nil` on `src`
  have e2 : Eval main (Pw.tLoop src Glyph.nil tmp 1) s1
      (Pw.tSt src Glyph.nil tmp 1 body rest s1) (5 * body.length + 7) :=
    Pw.tLoop_eval main src Glyph.nil tmp 1 h2 pw_nil_ne_eos body rest s1 h1src hnil
  set s2 : State := Pw.tSt src Glyph.nil tmp 1 body rest s1 with hs2
  have h2src : s2.stk src = Glyph.nil :: rest := by
    rw [hs2]; exact Pw.tSt_stk_k src Glyph.nil tmp 1 body rest s1 h2
  have h2tmp : s2.stk tmp = body.reverse ++ Pw.gM :: s.stk tmp := by
    rw [hs2, Pw.tSt_stk_dst, h1tmp]
  have h2o : ∀ j, j ≠ src → j ≠ tmp → s2.stk j = s1.stk j := by
    intro j hj1 hj2
    rw [hs2]; exact Pw.tSt_stk_ne src Glyph.nil tmp 1 body rest s1 hj1 hj2
  -- step 3: pop the terminal `nil` (register 0 then holds `Glyph.nil`)
  set s3 : State := State.tPop s2 src 0 with hs3
  have e3 : Eval main (.pop src 0) s2 s3 1 := by rw [hs3]; exact eval_pop main src 0 s2
  have h3src : s3.stk src = rest := by
    rw [hs3, Pw.tPop_stk, if_pos rfl, h2src, List.tail_cons]
  have h3reg : s3.reg 0 = Glyph.nil := by
    rw [hs3, Pw.tPop_reg, if_pos rfl, h2src, List.headD_cons]
  have h3o : ∀ j, j ≠ src → s3.stk j = s2.stk j := by
    intro j hj
    rw [hs3, Pw.tPop_stk, if_neg hj]
  -- step 4: push the marker `gM` on `dst`
  set s4a : State := State.tSet s3 1 Pw.gM with hs4a
  have e4a : Eval main (.set (1 : Reg) Pw.gM) s3 s4a 1 := by
    rw [hs4a]; exact eval_set main 1 Pw.gM s3
  set s4 : State := State.tPush s4a dst 1 with hs4
  have e4b : Eval main (.push dst 1) s4a s4 1 := by rw [hs4]; exact eval_push main dst 1 s4a
  have h4dst : s4.stk dst = Pw.gM :: s.stk dst := by
    rw [hs4, Pw.tPush_stk, if_pos rfl, hs4a, Pw.tSet_stk, Pw.tSet_reg, if_pos rfl]
    rw [h3o dst h1', h2o dst h1' h3', h1o dst h3']
  have h4src : s4.stk src = rest := by
    rw [hs4, Pw.tPush_stk, if_neg h1, hs4a, Pw.tSet_stk, h3src]
  have h4tmp : s4.stk tmp = body.reverse ++ Pw.gM :: s.stk tmp := by
    rw [hs4, Pw.tPush_stk, if_neg h3, hs4a, Pw.tSet_stk, h3o tmp h2, h2tmp]
  have h4reg : s4.reg 0 = Glyph.nil := by
    rw [hs4, Pw.tPush_reg, hs4a, Pw.tSet_reg, if_neg (by decide), h3reg]
  -- step 5: put the terminal `nil` back on `src`
  set s5 : State := State.tPush s4 src 0 with hs5
  have e5 : Eval main (.push src 0) s4 s5 1 := by rw [hs5]; exact eval_push main src 0 s4
  have h5reg : s5.reg 0 = Glyph.nil := by rw [hs5, Pw.tPush_reg, h4reg]
  have h5src : s5.stk src = Glyph.nil :: rest := by
    rw [hs5, Pw.tPush_stk, if_pos rfl, h4reg, h4src]
  have h5dst : s5.stk dst = Pw.gM :: s.stk dst := by
    rw [hs5, Pw.tPush_stk, if_neg h1', h4dst]
  have h5tmp : s5.stk tmp = body.reverse ++ Pw.gM :: s.stk tmp := by
    rw [hs5, Pw.tPush_stk, if_neg h2, h4tmp]
  -- step 6: put the `nil` on `dst` as well
  set s6 : State := State.tPush s5 dst 0 with hs6
  have e6 : Eval main (.push dst 0) s5 s6 1 := by rw [hs6]; exact eval_push main dst 0 s5
  have h6src : s6.stk src = Glyph.nil :: rest := by
    rw [hs6, Pw.tPush_stk, if_neg h1, h5src]
  have h6dst : s6.stk dst = Glyph.nil :: Pw.gM :: s.stk dst := by
    rw [hs6, Pw.tPush_stk, if_pos rfl, h5reg, h5dst]
  have h6tmp : s6.stk tmp = body.reverse ++ Pw.gM :: s.stk tmp := by
    rw [hs6, Pw.tPush_stk, if_neg h3, h5tmp]
  -- step 7: copy the block onto `src` and `dst`, in the right orientation
  obtain ⟨s7, n7, e7, hn7, h7tmp, h7src, h7dst, h7o⟩ :=
    Pw.tLoop2_eval main tmp Pw.gM src dst 1 h2' h3' h1 Pw.gM_ne_eos
      body.reverse (s.stk tmp) s6 h6tmp (fun g hg => hgM g (List.mem_reverse.mp hg))
  -- step 8: pop the scratch marker from `tmp`
  set s8 : State := State.tPop s7 tmp 0 with hs8
  have e8 : Eval main (.pop tmp 0) s7 s8 1 := by rw [hs8]; exact eval_pop main tmp 0 s7
  have h8tmp : s8.stk tmp = s.stk tmp := by
    rw [hs8, Pw.tPop_stk, if_pos rfl, h7tmp, List.tail_cons]
  have h8src : s8.stk src = body ++ Glyph.nil :: rest := by
    rw [hs8, Pw.tPop_stk, if_neg h2', h7src, h6src, List.reverse_reverse]
  have h8dst : s8.stk dst = body ++ Glyph.nil :: Pw.gM :: s.stk dst := by
    rw [hs8, Pw.tPop_stk, if_neg h3', h7dst, h6dst, List.reverse_reverse]
  have hfsrc : s8.stk src = (ofList xs).enc ++ rest := by
    rw [h8src, hbody, List.append_assoc, List.singleton_append]
  have hfdst : s8.stk dst = (ofList xs).enc ++ Pw.gM :: s.stk dst := by
    rw [h8dst, hbody, List.append_assoc, List.singleton_append]
  have hother : ∀ j, j ≠ src → j ≠ dst → j ≠ tmp → s8.stk j = s.stk j := by
    intro j hj1 hj2 hj3
    rw [hs8, Pw.tPop_stk, if_neg hj3]
    rw [h7o j hj3 hj1 hj2]
    rw [hs6, Pw.tPush_stk, if_neg hj2]
    rw [hs5, Pw.tPush_stk, if_neg hj1]
    rw [hs4, Pw.tPush_stk, if_neg hj2]
    rw [hs4a, Pw.tSet_stk]
    rw [h3o j hj1, h2o j hj1 hj3, h1o j hj3]
  have hlen : (ofList xs).enc.length + 1 = body.length + 2 := by rw [hbody]; simp
  have hn7' : n7 ≤ 7 * body.length + 8 := by
    have := hn7
    rw [List.length_reverse] at this
    exact this
  have eall : Eval main (copyBlockProg src dst tmp 0 1) s s8
      (1 + (1 + ((5 * body.length + 7) + (1 + (1 + (1 + (1 + (1 + (n7 + 1))))))))) :=
    Eval.seq e1a (Eval.seq e1b (Eval.seq e2 (Eval.seq e3 (Eval.seq e4a (Eval.seq e4b
      (Eval.seq e5 (Eval.seq e6 (Eval.seq e7 e8))))))))
  refine ⟨s8, _, eall, ?_, hfsrc, hfdst, h8tmp, hother⟩
  · rw [hlen]; omega

end Work.Transform
