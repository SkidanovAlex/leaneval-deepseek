import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Move
import Submission.Work.Kernel.dropValue
import Submission.Work.Kernel.zipWithDefs
import Submission.Work.Kernel.zipWith_setup_ev
import Submission.Work.Kernel.zipWith_rebuild_ev

set_option autoImplicit false

namespace Work.Kernel

open HvdH
open Work.Layout

/-!
# Kernel: `zipWith` — proof

The program is defined and documented in `Submission/Work/Kernel/zipWithDefs.lean`.  Here we prove
the `zipWith` field of `HvdH.KernelLib`.

* `zipWith_stop_ev` — the last iteration of the main loop (both lists exhausted);
* `zipWith_mainLoop_ev` — the main loop, by induction on the number of remaining elements;
* `zipWith_finish_ev` — the cleanup (two `nil` pops, push `nil`) followed by the rebuild loop;
* `zipWith_all_ev` — the whole program;
* `zipWith` — the statement of `HvdH.KernelLib.zipWith`.
-/

set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

theorem zipWith_aux_vsz_snoc {p : List Val} {z : Val} {L : ℕ}
    (h : ∀ i < p.length, vsz (p.getD i .nil) ≤ L) (hz : vsz z ≤ L) :
    ∀ i < (p ++ [z]).length, vsz ((p ++ [z]).getD i .nil) ≤ L := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i p.length with hlt | hge
  · rw [List.getD_append p [z] .nil i hlt]; exact h i hlt
  · have hi' : i = p.length := by omega
    rw [hi', List.getD_append_right p [z] .nil p.length (le_refl _)]
    simp only [Nat.sub_self, List.getD_cons_zero]
    exact hz

theorem zipWith_cost_le (n c L n1 n2 n3 : ℕ)
    (h1 : n1 ≤ 3 + 16 * (n * (L + 1) + 2) + 16 * (n * (L + 1) + 2))
    (h2 : n2 ≤ n * (c + 48 * (L + 1) + 8) + 5)
    (h3 : n3 ≤ 5 + (n * (16 * (L + 1) + 6) + 6)) :
    n1 + (n2 + n3) ≤ n * (c + 256 * (L + 1)) + 256 := by
  have hA : n ≤ n * (L + 1) := by
    have := Nat.mul_le_mul_left n (Nat.succ_le_succ (Nat.zero_le L))
    simpa using this
  have e1 : n * (c + 48 * (L + 1) + 8) = n * c + 48 * (n * (L + 1)) + 8 * n := by ring
  have e2 : n * (16 * (L + 1) + 6) = 16 * (n * (L + 1)) + 6 * n := by ring
  have e3 : n * (c + 256 * (L + 1)) = n * c + 256 * (n * (L + 1)) := by ring
  rw [e1] at h2
  rw [e2] at h3
  rw [e3]
  omega

theorem zipWith_aux_tPush_stk (s : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPush s k r).stk j = if j = k then s.reg r :: s.stk k else s.stk j := by
  simp [State.tPush, State.updStk_apply]

theorem zipWith_aux_tPop_stk (s : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPop s k r).stk j = if j = k then (s.stk k).tail else s.stk j := by
  simp [State.tPop, State.updStk_apply, State.updReg_stk]

theorem zipWith_aux_tSet_stk (s : State) (r : Reg) (g : Glyph) (j : Stk) :
    (State.tSet s r g).stk j = s.stk j := by
  simp [State.tSet, State.updReg_stk]

theorem zipWith_aux_tSet_reg_self (s : State) (r : Reg) (g : Glyph) :
    (State.tSet s r g).reg r = g := by
  simp [State.tSet, State.updReg]

/-! ## One iteration of the main loop -/

theorem zipWith_aux_getD_mem {l : List Val} {k : ℕ} (h : k < l.length) :
    l.getD k .nil ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem zipWith_aux_ofList_drop_enc {l : List Val} {k : ℕ} (h : k < l.length) :
    (ofList (l.drop k)).enc =
      Glyph.cons :: ((l.getD k .nil).enc ++ (ofList (l.drop (k + 1))).enc) :=
  zipWith_ofList_drop_enc h

set_option maxHeartbeats 1600000 in
theorem zipWith_aux_step_ev (main q : Cmd) (rest0 : List Val) (P : Val → Val → Prop)
    (Q : Val → Val → Val → Prop) (c L : ℕ)
    (hq : ∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: rest0)
      (fun _ out => ∃ z, out = z :: rest0 ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c)) :
    ∀ (X0 Y0 p : List Val) (s : State) (B1 B2 B3 R : List Glyph),
      p.length < X0.length → p.length < Y0.length →
      (∀ i < X0.length, P (X0.getD i .nil) (Y0.getD i .nil)) →
      (∀ x ∈ X0 ++ Y0, vsz x ≤ L) →
      s.stk 1 = (ofList (X0.drop p.length)).enc ++ B1 →
      s.stk 2 = (ofList (Y0.drop p.length)).enc ++ B2 →
      s.stk 3 = encs p.reverse ++ gMark :: B3 →
      s.stk 0 = encs rest0 ++ R →
      s.reg rLoopG = Glyph.cons →
      ∃ (z : Val) (s' : State) (n : ℕ),
        Eval main (zipWith_body q) s s' n ∧ n ≤ c + 48 * (L + 1) + 7 ∧
        Q (X0.getD p.length .nil) (Y0.getD p.length .nil) z ∧ vsz z ≤ L ∧
        s'.stk 1 = (ofList (X0.drop (p.length + 1))).enc ++ B1 ∧
        s'.stk 2 = (ofList (Y0.drop (p.length + 1))).enc ++ B2 ∧
        s'.stk 3 = encs (p ++ [z]).reverse ++ gMark :: B3 ∧
        s'.stk 0 = encs rest0 ++ R ∧ s'.reg rLoopG = Glyph.cons ∧
        (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → s'.stk j = s.stk j) := by
  intro X0 Y0 p s B1 B2 B3 R hltX hltY hP hL h1 h2 h3 h0 hr
  set x : Val := X0.getD p.length .nil with hx
  set y : Val := Y0.getD p.length .nil with hy
  have hs1 : s.stk 1 = Glyph.cons :: (x.enc ++ ((ofList (X0.drop (p.length + 1))).enc ++ B1)) := by
    rw [h1, zipWith_aux_ofList_drop_enc hltX, hx]
    simp only [List.cons_append, List.append_assoc]
  have hs2 : s.stk 2 = Glyph.cons :: (y.enc ++ ((ofList (Y0.drop (p.length + 1))).enc ++ B2)) := by
    rw [h2, zipWith_aux_ofList_drop_enc hltY, hy]
    simp only [List.cons_append, List.append_assoc]
  have hxL : vsz x ≤ L := hL x (List.mem_append_left _ (zipWith_aux_getD_mem hltX))
  have hyL : vsz y ≤ L := hL y (List.mem_append_right _ (zipWith_aux_getD_mem hltY))
  have hPxy : P x y := hP p.length hltX
  -- peek
  have hne_mark : (s.stk 1).headD Glyph.eos = Glyph.cons := by rw [hs1]; rfl
  set sp : State := ⟨Function.update s.reg rA ((s.stk 1).headD Glyph.eos), s.stk⟩ with hsp
  have hsp_stk : ∀ j, sp.stk j = s.stk j := by intro j; rw [hsp]
  have hsp_reg : sp.reg rA = Glyph.cons := by rw [hsp]; simp only [regUpd_same]; exact hne_mark
  have hev1 : Ev main (.peek 1 rA) s sp 1 := by rw [hsp]; exact ev_peek main 1 rA s
  -- pop 1
  set s1 : State := State.tPop sp 1 rA with hs1def
  have hev2 : Ev main (.pop 1 rA) sp s1 1 := by rw [hs1def]; exact ev_pop main 1 rA sp
  have hs1_1 : s1.stk 1 = x.enc ++ ((ofList (X0.drop (p.length + 1))).enc ++ B1) := by
    rw [hs1def, zipWith_aux_tPop_stk, if_pos (rfl : (1 : Stk) = 1), hsp_stk 1, hs1]
    rfl
  have hs1_other : ∀ j, j ≠ 1 → s1.stk j = sp.stk j := by
    intro j hj
    rw [hs1def, zipWith_aux_tPop_stk, if_neg hj]
  -- pop 2
  set s2 : State := State.tPop s1 2 rA with hs2def
  have hev3 : Ev main (.pop 2 rA) s1 s2 1 := by rw [hs2def]; exact ev_pop main 2 rA s1
  have hs2_2 : s2.stk 2 = y.enc ++ ((ofList (Y0.drop (p.length + 1))).enc ++ B2) := by
    rw [hs2def, zipWith_aux_tPop_stk, if_pos (rfl : (2 : Stk) = 2), hs1_other 2 (by decide), hsp_stk 2, hs2]
    rfl
  have hs2_other : ∀ j, j ≠ 2 → s2.stk j = s1.stk j := by
    intro j hj
    rw [hs2def, zipWith_aux_tPop_stk, if_neg hj]
  have hs2_1 : s2.stk 1 = x.enc ++ ((ofList (X0.drop (p.length + 1))).enc ++ B1) := by
    rw [hs2_other 1 (by decide)]; exact hs1_1
  have hs2_0 : s2.stk 0 = encs rest0 ++ R := by
    rw [hs2_other 0 (by decide), hs1_other 0 (by decide), hsp_stk 0]; exact h0
  -- mvVal 2 0 4 5
  obtain ⟨s3, n3, hev4, hn3, hs3_2, hs3_0, hs3_4, hs3_5, hfr3⟩ :=
    mvVal_ev_full (main := main) (a := (2 : Stk)) (b := (0 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s2.reg) (X := s2.stk) (v := y)
      (A := (ofList (Y0.drop (p.length + 1))).enc ++ B2) (B := s2.stk 0) hs2_2 rfl
  have hs3_0' : s3.stk 0 = y.enc ++ (encs rest0 ++ R) := by rw [hs3_0, hs2_0]
  have hs3_1 : s3.stk 1 = x.enc ++ ((ofList (X0.drop (p.length + 1))).enc ++ B1) := by
    rw [hfr3 1 (by decide) (by decide) (by decide) (by decide)]; exact hs2_1
  have hs3_3 : s3.stk 3 = encs p.reverse ++ gMark :: B3 := by
    rw [hfr3 3 (by decide) (by decide) (by decide) (by decide),
      hs2_other 3 (by decide), hs1_other 3 (by decide), hsp_stk 3]
    exact h3
  -- mvVal 1 0 4 5
  obtain ⟨s4, n4, hev5, hn4, hs4_1, hs4_0, hs4_4, hs4_5, hfr4⟩ :=
    mvVal_ev_full (main := main) (a := (1 : Stk)) (b := (0 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s3.reg) (X := s3.stk) (v := x)
      (A := (ofList (X0.drop (p.length + 1))).enc ++ B1) (B := s3.stk 0) hs3_1 rfl
  have hs4_0' : s4.stk 0 = encs (x :: y :: rest0) ++ R := by
    rw [hs4_0, hs3_0']
    simp only [encs_cons, List.append_assoc]
  -- run q
  obtain ⟨out, s5, n5, hpost, hev6, hn5, hs5_0, hfr5⟩ :=
    hq x y hPxy (x :: y :: rest0) rfl s4 R hs4_0'
  obtain ⟨z, hz, hQz, hzL⟩ := hpost
  subst hz
  have hs4_3 : s4.stk 3 = encs p.reverse ++ gMark :: B3 := by
    rw [hfr4 3 (by decide) (by decide) (by decide) (by decide)]; exact hs3_3
  -- mvVal 0 3 4 5
  have hs5_0' : s5.stk 0 = z.enc ++ (encs rest0 ++ R) := by
    rw [hs5_0]; simp only [encs_cons, List.append_assoc]
  obtain ⟨s6, n6, hev7, hn6, hs6_0, hs6_3, hs6_4, hs6_5, hfr6⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := (3 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s5.reg) (X := s5.stk) (v := z) (A := encs rest0 ++ R) (B := s5.stk 3) hs5_0' rfl
  have hs6_3' : s6.stk 3 = encs (p ++ [z]).reverse ++ gMark :: B3 := by
    rw [hs6_3, hfr5 3 (by decide), hs4_3]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, encs_cons, List.append_assoc]
  -- set rLoopG cons
  set s7 : State := State.tSet s6 rLoopG Glyph.cons with hs7def
  have hev8 : Ev main (.set rLoopG Glyph.cons) s6 s7 1 := by rw [hs7def]; exact ev_set main rLoopG Glyph.cons s6
  have hs7_reg : s7.reg rLoopG = Glyph.cons := by rw [hs7def]; exact zipWith_aux_tSet_reg_self s6 rLoopG Glyph.cons
  have hframe : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → s7.stk j = s.stk j := by
    intro j hj0 hj1 hj2 hj3
    rcases eq_or_ne j (4 : Stk) with h4 | h4
    · subst h4
      rw [hs7def, zipWith_aux_tSet_stk, hs6_4, hfr5 4 (by decide), hs4_4, hs3_4,
        hs2_other 4 (by decide), hs1_other 4 (by decide), hsp_stk 4]
    · rcases eq_or_ne j (5 : Stk) with h5 | h5
      · subst h5
        rw [hs7def, zipWith_aux_tSet_stk, hs6_5, hfr5 5 (by decide), hs4_5, hs3_5,
          hs2_other 5 (by decide), hs1_other 5 (by decide), hsp_stk 5]
      · rw [hs7def, zipWith_aux_tSet_stk, hfr6 j hj0 hj3 h4 h5, hfr5 j hj0, hfr4 j hj1 hj0 h4 h5,
          hfr3 j hj2 hj0 h4 h5, hs2_other j hj2, hs1_other j hj1, hsp_stk j]
  -- assemble the Eval
  have hpop1 : Ev main (.pop 1 rA) sp s1 1 := hev2
  have hpop2 : Ev main (.pop 2 rA) s1 s2 1 := hev3
  have hmv1 : Ev main (mvVal 2 0 4 5) s2 s3 (16 * (L + 1)) := hev4.mono (by omega)
  have hmv2 : Ev main (mvVal 1 0 4 5) s3 s4 (16 * (L + 1)) := hev5.mono (by omega)
  have hq' : Ev main q s4 s5 c := ⟨n5, hev6, hn5⟩
  have hmv3 : Ev main (mvVal 0 3 4 5) s5 s6 (16 * (L + 1)) := hev7.mono (by omega)
  have hlast : Ev main (Cmd.seq (mvVal 0 3 4 5) (.set rLoopG Glyph.cons)) s5 s7
      (16 * (L + 1) + 1) := Ev.seq hmv3 hev8
  have e48 : 48 * (L + 1) = 16 * (L + 1) + 16 * (L + 1) + 16 * (L + 1) := by ring
  have hA : Ev main (Cmd.seq (mvVal 2 0 4 5)
      (Cmd.seq (mvVal 1 0 4 5) (Cmd.seq q (Cmd.seq (mvVal 0 3 4 5) (.set rLoopG Glyph.cons)))))
      s2 s7 (16 * (L + 1) + (16 * (L + 1) + (c + (16 * (L + 1) + 1)))) :=
    Ev.seq hmv1 (Ev.seq hmv2 (Ev.seq hq' hlast))
  have hB : Ev main (Cmd.seq (.pop 2 rA)
      (Cmd.seq (mvVal 2 0 4 5)
        (Cmd.seq (mvVal 1 0 4 5) (Cmd.seq q (Cmd.seq (mvVal 0 3 4 5) (.set rLoopG Glyph.cons))))))
      s1 s7 (1 + (16 * (L + 1) + (16 * (L + 1) + (c + (16 * (L + 1) + 1))))) :=
    Ev.seq hpop2 hA
  have hC : Ev main (zipWith_bodyThen q) sp s7
      (1 + (1 + (16 * (L + 1) + (16 * (L + 1) + (c + (16 * (L + 1) + 1)))))) :=
    Ev.seq hpop1 hB
  have hbodyA : Ev main (zipWith_bodyThen q) sp s7
      (c + (16 * (L + 1) + 16 * (L + 1) + 16 * (L + 1)) + 5) := hC.mono (by omega)
  have hallA : Ev main (zipWith_body q) s s7
      (c + (16 * (L + 1) + 16 * (L + 1) + 16 * (L + 1)) + 7) :=
    (Ev.seq hev1 (Ev.iteT hsp_reg hbodyA)).mono (by omega)
  have hall : Ev main (zipWith_body q) s s7 (c + 48 * (L + 1) + 7) := by
    rw [e48]
    exact hallA
  obtain ⟨n, hev, hn⟩ := hall
  have hQz' : Q (X0.getD p.length .nil) (Y0.getD p.length .nil) z := by
    rw [hx, hy] at hQz
    exact hQz
  have hF1 : s7.stk 1 = (ofList (X0.drop (p.length + 1))).enc ++ B1 := by
    rw [hs7def, zipWith_aux_tSet_stk,
      hfr6 1 (by decide) (by decide) (by decide) (by decide), hfr5 1 (by decide)]
    exact hs4_1
  have hF2 : s7.stk 2 = (ofList (Y0.drop (p.length + 1))).enc ++ B2 := by
    rw [hs7def, zipWith_aux_tSet_stk,
      hfr6 2 (by decide) (by decide) (by decide) (by decide), hfr5 2 (by decide),
      hfr4 2 (by decide) (by decide) (by decide) (by decide)]
    exact hs3_2
  have hF0 : s7.stk 0 = encs rest0 ++ R := by
    rw [hs7def, zipWith_aux_tSet_stk]; exact hs6_0
  exact ⟨z, s7, n, hev, by omega, hQz', hzL, hF1, hF2, hs6_3', hF0, hs7_reg, hframe⟩


/-! ## The stop iteration of the main loop -/

theorem zipWith_stop_ev (main q : Cmd) :
    ∀ (X0 Y0 p : List Val) (s : State) (B1 B2 B3 R : List Glyph) (rest0 : List Val),
      p.length = X0.length → p.length = Y0.length →
      s.stk 1 = (ofList (X0.drop p.length)).enc ++ B1 →
      s.stk 2 = (ofList (Y0.drop p.length)).enc ++ B2 →
      s.stk 3 = encs p.reverse ++ gMark :: B3 →
      s.stk 0 = encs rest0 ++ R →
      s.reg rLoopG = Glyph.cons →
      ∃ s' n, Eval main (zipWith_body q) s s' n ∧ n ≤ 3 ∧
        s'.reg rLoopG = Glyph.eos ∧ (∀ j : Stk, s'.stk j = s.stk j) := by
  intro X0 Y0 p s B1 B2 B3 R rest0 hX hY h1 h2 h3 h0 hr
  have hdrop : X0.drop p.length = ([] : List Val) := by rw [hX, List.drop_length]
  have h1' : s.stk 1 = Glyph.nil :: B1 := by rw [h1, hdrop]; rfl
  have hhead : (s.stk 1).headD Glyph.eos = Glyph.nil := by rw [h1']; rfl
  have hne : (⟨Function.update s.reg rA ((s.stk 1).headD Glyph.eos), s.stk⟩ : State).reg rA ≠
      Glyph.cons := by
    simp only [regUpd_same, hhead]
    intro hh
    cases hh
  refine ⟨⟨Function.update (Function.update s.reg rA ((s.stk 1).headD Glyph.eos)) rLoopG Glyph.eos,
    s.stk⟩, 3, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq (Eval.peek 1 rA s) (Eval.iteF hne
      (Eval.set rLoopG Glyph.eos ⟨Function.update s.reg rA ((s.stk 1).headD Glyph.eos), s.stk⟩))
  · omega
  · simp only [regUpd_same]
  · intro j; rfl

/-! ## The main loop -/

theorem zipWith_mainLoop_ev
    (main q : Cmd) (rest0 : List Val) (P : Val → Val → Prop) (Q : Val → Val → Val → Prop)
    (c L : ℕ)
    (hq : ∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: rest0)
      (fun _ out => ∃ z, out = z :: rest0 ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c))
    (X0 Y0 : List Val) (hXY : X0.length = Y0.length)
    (hP : ∀ i < X0.length, P (X0.getD i .nil) (Y0.getD i .nil))
    (hL : ∀ x ∈ X0 ++ Y0, vsz x ≤ L) :
    ∀ m (p : List Val) (s : State) (B1 B2 B3 R : List Glyph),
      p.length + m = X0.length →
      zipWith_corr Q X0 Y0 p →
      (∀ i < p.length, vsz (p.getD i .nil) ≤ L) →
      s.stk 1 = (ofList (X0.drop p.length)).enc ++ B1 →
      s.stk 2 = (ofList (Y0.drop p.length)).enc ++ B2 →
      s.stk 3 = encs p.reverse ++ gMark :: B3 →
      s.stk 0 = encs rest0 ++ R →
      s.reg rLoopG = Glyph.cons →
      ∃ (p' : List Val) (s' : State) (n : ℕ),
        Eval main (zipWith_loopProg q) s s' n ∧
        n ≤ m * (c + 48 * (L + 1) + 8) + 5 ∧
        p'.length = X0.length ∧ zipWith_corr Q X0 Y0 p' ∧
        (∀ i < p'.length, vsz (p'.getD i .nil) ≤ L) ∧
        s'.stk 1 = (ofList (X0.drop p'.length)).enc ++ B1 ∧
        s'.stk 2 = (ofList (Y0.drop p'.length)).enc ++ B2 ∧
        s'.stk 3 = encs p'.reverse ++ gMark :: B3 ∧
        s'.stk 0 = encs rest0 ++ R ∧
        (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → s'.stk j = s.stk j) := by
  intro m
  induction m with
  | zero =>
    intro p s B1 B2 B3 R hpm hcorr hsizes h1 h2 h3 h0 hr
    have hX : p.length = X0.length := by omega
    have hY : p.length = Y0.length := by omega
    obtain ⟨s1, n1, hev1, hn1, hreg1, hstk1⟩ :=
      zipWith_stop_ev main q X0 Y0 p s B1 B2 B3 R rest0 hX hY h1 h2 h3 h0 hr
    have hne : s1.reg rLoopG ≠ Glyph.cons := by rw [hreg1]; decide
    refine ⟨p, s1, n1 + 1 + 1, Eval.loopT hr hev1 (Eval.loopF hne), ?_, hX, hcorr, hsizes,
      ?_, ?_, ?_, ?_, ?_⟩
    · have := hn1; omega
    · rw [hstk1 1]; exact h1
    · rw [hstk1 2]; exact h2
    · rw [hstk1 3]; exact h3
    · rw [hstk1 0]; exact h0
    · intro j hj0 hj1 hj2 hj3; rw [hstk1 j]
  | succ m ih =>
    intro p s B1 B2 B3 R hpm hcorr hsizes h1 h2 h3 h0 hr
    have hltX : p.length < X0.length := by omega
    have hltY : p.length < Y0.length := by omega
    obtain ⟨z, s1, n1, hev1, hn1, hQz, hLz, hs1_1, hs1_2, hs1_3, hs1_0, hreg1, hframe1⟩ :=
      zipWith_aux_step_ev main q rest0 P Q c L hq X0 Y0 p s B1 B2 B3 R
        hltX hltY hP hL h1 h2 h3 h0 hr
    have hlen' : (p ++ [z]).length + m = X0.length := by
      simp only [List.length_append, List.length_singleton]; omega
    have hs1_1' : s1.stk 1 = (ofList (X0.drop (p ++ [z]).length)).enc ++ B1 := by
      rw [List.length_append, List.length_singleton]; exact hs1_1
    have hs1_2' : s1.stk 2 = (ofList (Y0.drop (p ++ [z]).length)).enc ++ B2 := by
      rw [List.length_append, List.length_singleton]; exact hs1_2
    have hcorr' : zipWith_corr Q X0 Y0 (p ++ [z]) := zipWith_corr_snoc hcorr hltX hltY hQz
    have hsizes' : ∀ i < (p ++ [z]).length, vsz ((p ++ [z]).getD i .nil) ≤ L :=
      zipWith_aux_vsz_snoc hsizes hLz
    obtain ⟨p', s2, n2, hev2, hn2, hp'len, hcorr'', hsizes'', hs2_1, hs2_2, hs2_3, hs2_0,
      hframe2⟩ :=
      ih (p ++ [z]) s1 B1 B2 B3 R hlen' hcorr' hsizes' hs1_1' hs1_2' hs1_3 hs1_0 hreg1
    refine ⟨p', s2, n1 + n2 + 1, Eval.loopT hr hev1 hev2, ?_, hp'len, hcorr'', hsizes'',
      hs2_1, hs2_2, hs2_3, hs2_0, ?_⟩
    · calc n1 + n2 + 1 ≤ (c + 48 * (L + 1) + 7) + (m * (c + 48 * (L + 1) + 8) + 5) + 1 := by
            omega
        _ = (m + 1) * (c + 48 * (L + 1) + 8) + 5 := by ring
    · intro j hj0 hj1 hj2 hj3
      rw [hframe2 j hj0 hj1 hj2 hj3]
      exact hframe1 j hj0 hj1 hj2 hj3

/-! ## Cleanup and rebuild -/

theorem zipWith_finish_ev (main : Cmd) (L : ℕ) :
    ∀ (w : List Val) (s : State) (B3 R : List Glyph) (rest0 : List Val) (B1 B2 : List Glyph),
      (∀ v ∈ w, vsz v ≤ L) →
      s.stk 1 = Glyph.nil :: B1 → s.stk 2 = Glyph.nil :: B2 →
      s.stk 3 = encs w ++ gMark :: B3 →
      s.stk 0 = encs rest0 ++ R →
      ∃ s' n, Eval main zipWith_finishCmd s s' n ∧
        n ≤ 5 + (w.length * (16 * (L + 1) + 6) + 6) ∧
        s'.stk 0 = encs (ofList w.reverse :: rest0) ++ R ∧
        s'.stk 1 = B1 ∧ s'.stk 2 = B2 ∧ s'.stk 3 = B3 ∧
        (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → s'.stk j = s.stk j) := by
  intro w s B3 R rest0 B1 B2 hLw h1 h2 h3 h0
  set sp1 : State := State.tPop s 1 rA with hp1
  set sp2 : State := State.tPop sp1 2 rA with hp2
  set sp3 : State := State.tSet sp2 rB Glyph.nil with hp3
  set sp4 : State := State.tPush sp3 0 rB with hp4
  set sp5 : State := State.tSet sp4 rLoopG Glyph.cons with hp5
  have hev1 : Ev main (.pop 1 rA) s sp1 1 := by rw [hp1]; exact ev_pop main 1 rA s
  have hev2 : Ev main (.pop 2 rA) sp1 sp2 1 := by rw [hp2]; exact ev_pop main 2 rA sp1
  have hev3 : Ev main (.set rB Glyph.nil) sp2 sp3 1 := by rw [hp3]; exact ev_set main rB Glyph.nil sp2
  have hev4 : Ev main (.push 0 rB) sp3 sp4 1 := by rw [hp4]; exact ev_push main 0 rB sp3
  have hev5 : Ev main (.set rLoopG Glyph.cons) sp4 sp5 1 :=
    by rw [hp5]; exact ev_set main rLoopG Glyph.cons sp4
  have hsp5_1 : sp5.stk 1 = B1 := by
    rw [hp5, hp4, hp3, hp2, hp1]
    simp only [zipWith_aux_tSet_stk, zipWith_aux_tPush_stk, zipWith_aux_tPop_stk, h1]
    simp
  have hsp5_2 : sp5.stk 2 = B2 := by
    rw [hp5, hp4, hp3, hp2, hp1]
    simp only [zipWith_aux_tSet_stk, zipWith_aux_tPush_stk, zipWith_aux_tPop_stk, h2]
    simp
  have hsp5_0 : sp5.stk 0 = encs (ofList ([] : List Val) :: rest0) ++ R := by
    rw [hp5, hp4, hp3, hp2, hp1]
    simp only [zipWith_aux_tSet_stk, zipWith_aux_tPush_stk, zipWith_aux_tPop_stk, zipWith_aux_tSet_reg_self, h0]
    simp [encs, Val.enc, List.append_assoc]
  have hsp5_3 : sp5.stk 3 = encs w ++ gMark :: B3 := by
    rw [hp5, hp4, hp3, hp2, hp1]
    simp only [zipWith_aux_tSet_stk, zipWith_aux_tPush_stk, zipWith_aux_tPop_stk, h3]
    simp
  have hsp5_reg : sp5.reg rLoopG = Glyph.cons := by
    rw [hp5]; exact zipWith_aux_tSet_reg_self sp4 rLoopG Glyph.cons
  have hsp5_fr : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → sp5.stk j = s.stk j := by
    intro j hj0 hj1 hj2 hj3
    rw [hp5, hp4, hp3, hp2, hp1]
    simp only [zipWith_aux_tSet_stk, zipWith_aux_tPush_stk, zipWith_aux_tPop_stk]
    simp [hj0, hj1, hj2, hj3]
  obtain ⟨s6, n6, hev6, hn6, hs6_0, hs6_3, hframe6⟩ :=
    zipWith_rebuild_ev main L w ([] : List Val) sp5 B3 R rest0 hLw hsp5_3 hsp5_0 hsp5_reg
  have h34 : Ev main (Cmd.seq (.set rB Glyph.nil) (.push 0 rB)) sp2 sp4 2 := Ev.seq hev3 hev4
  have h56 : Ev main (Cmd.seq (.set rLoopG Glyph.cons) zipWith_rebuildProg) sp4 s6 (1 + n6) :=
    Ev.seq hev5 ⟨n6, hev6, le_refl n6⟩
  have hall : Ev main zipWith_finishCmd s s6 (5 + n6) := by
    show Ev main (Cmd.seq (.pop 1 rA)
      (Cmd.seq (.pop 2 rA)
        (Cmd.seq (Cmd.seq (.set rB Glyph.nil) (.push 0 rB))
          (Cmd.seq (.set rLoopG Glyph.cons) zipWith_rebuildProg)))) s s6 (5 + n6)
    exact (Ev.seq hev1 (Ev.seq hev2 (Ev.seq h34 h56))).mono (by omega)
  obtain ⟨n, hev, hn⟩ := hall
  refine ⟨s6, n, hev, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hn; have := hn6; omega
  · rw [hs6_0, List.append_nil]
  · rw [hframe6 1 (by decide) (by decide)]; exact hsp5_1
  · rw [hframe6 2 (by decide) (by decide)]; exact hsp5_2
  · exact hs6_3
  · intro j hj0 hj1 hj2 hj3
    rw [hframe6 j hj0 hj3, hsp5_fr j hj0 hj1 hj2 hj3]

/-! ## Assembly: the whole program -/

theorem zipWith_all_ev (main q : Cmd) (rest0 : List Val) (P : Val → Val → Prop)
    (Q : Val → Val → Val → Prop) (c L : ℕ)
    (hq : ∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: rest0)
      (fun _ out => ∃ z, out = z :: rest0 ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c)) :
    ∀ (X0 Y0 : List Val) (s : State) (R : List Glyph),
      X0.length = Y0.length →
      (∀ i < X0.length, P (X0.getD i .nil) (Y0.getD i .nil)) →
      (∀ x ∈ X0 ++ Y0, vsz x ≤ L) →
      s.stk 0 = encs (ofList X0 :: ofList Y0 :: rest0) ++ R →
      ∃ (p' : List Val) (s' : State) (n : ℕ),
        Eval main (zipWith_prog q) s s' n ∧
        n ≤ X0.length * (c + 256 * (L + 1)) + 256 ∧
        p'.length = X0.length ∧
        (∀ i < X0.length, Q (X0.getD i .nil) (Y0.getD i .nil) (p'.getD i .nil)) ∧
        s'.stk 0 = encs (ofList p' :: rest0) ++ R ∧
        (∀ j, j ≠ 0 → s'.stk j = s.stk j) := by
  intro X0 Y0 s R hXY hP hL h0
  obtain ⟨s1, n1, hev1, hn1, hs1_0, hs1_1, hs1_2, hs1_3, hs1_reg, hframe1⟩ :=
    zipWith_setup_ev main X0 Y0 rest0 R s h0
  have hsizes0 : ∀ i < ([] : List Val).length, vsz (([] : List Val).getD i .nil) ≤ L := by
    intro i hi; simp at hi
  have h1' : s1.stk 1 = (ofList (X0.drop ([] : List Val).length)).enc ++ s.stk 1 := by
    rw [List.length_nil, List.drop_zero]; exact hs1_1
  have h2' : s1.stk 2 = (ofList (Y0.drop ([] : List Val).length)).enc ++ s.stk 2 := by
    rw [List.length_nil, List.drop_zero]; exact hs1_2
  have h3' : s1.stk 3 = encs ([] : List Val).reverse ++ gMark :: s.stk 3 := by
    rw [List.reverse_nil, encs_nil]; exact hs1_3
  obtain ⟨p', s2, n2, hev2, hn2, hp'len, hcorr, hsizes, hs2_1, hs2_2, hs2_3, hs2_0, hframe2⟩ :=
    zipWith_mainLoop_ev main q rest0 P Q c L hq X0 Y0 hXY hP hL X0.length ([] : List Val) s1
      (s.stk 1) (s.stk 2) (s.stk 3) R
      (by simp) (zipWith_corr_nil Q X0 Y0) hsizes0 h1' h2' h3' hs1_0 hs1_reg
  have hdrop1 : X0.drop p'.length = ([] : List Val) := by rw [hp'len, List.drop_length]
  have hdrop1' : Y0.drop p'.length = ([] : List Val) := by rw [hp'len, hXY, List.drop_length]
  have hs2_1' : s2.stk 1 = Glyph.nil :: s.stk 1 := by rw [hs2_1, hdrop1]; rfl
  have hs2_2' : s2.stk 2 = Glyph.nil :: s.stk 2 := by rw [hs2_2, hdrop1']; rfl
  have hLrev : ∀ v ∈ p'.reverse, vsz v ≤ L := by
    intro v hv
    rw [List.mem_reverse] at hv
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hv
    have h := hsizes i hi
    rw [List.getD_eq_getElem _ _ hi, hiv] at h
    exact h
  obtain ⟨s3, n3, hev3, hn3, hs3_0, hs3_1, hs3_2, hs3_3, hframe3⟩ :=
    zipWith_finish_ev main L p'.reverse s2 (s.stk 3) R rest0 (s.stk 1) (s.stk 2) hLrev hs2_1' hs2_2'
      hs2_3 hs2_0
  refine ⟨p', s3, n1 + (n2 + n3), ?_, ?_, hp'len, ?_, ?_, ?_⟩
  · show Eval main (Cmd.seq zipWith_setupCmd (Cmd.seq (zipWith_loopProg q) zipWith_finishCmd)) s s3
      (n1 + (n2 + n3))
    exact Eval.seq hev1 (Eval.seq hev2 hev3)
  · have hvX : vsz (ofList X0) ≤ X0.length * (L + 1) + 1 :=
      zipWith_vsz_ofList_le X0 (fun x hx => hL x (List.mem_append_left _ hx))
    have hvY : vsz (ofList Y0) ≤ X0.length * (L + 1) + 1 := by
      have h := zipWith_vsz_ofList_le Y0 (fun x hx => hL x (List.mem_append_right _ hx))
      rw [← hXY] at h
      exact h
    have hn1' : n1 ≤ 3 + 16 * (X0.length * (L + 1) + 2) + 16 * (X0.length * (L + 1) + 2) := by
      have ha : 16 * (vsz (ofList X0) + 1) ≤ 16 * (X0.length * (L + 1) + 2) :=
        Nat.mul_le_mul_left 16 (by omega)
      have hb : 16 * (vsz (ofList Y0) + 1) ≤ 16 * (X0.length * (L + 1) + 2) :=
        Nat.mul_le_mul_left 16 (by omega)
      have := hn1; omega
    have hn3' : n3 ≤ 5 + (X0.length * (16 * (L + 1) + 6) + 6) := by
      calc n3 ≤ 5 + (p'.reverse.length * (16 * (L + 1) + 6) + 6) := hn3
        _ = 5 + (X0.length * (16 * (L + 1) + 6) + 6) := by rw [List.length_reverse, hp'len]
    exact zipWith_cost_le X0.length c L n1 n2 n3 hn1' hn2 hn3'
  · intro i hi
    exact hcorr.2.2 i (by rw [hp'len]; exact hi)
  · rw [hs3_0]; simp
  · intro j hj
    by_cases hj1 : j = 1
    · subst hj1; exact hs3_1
    by_cases hj2 : j = 2
    · subst hj2; exact hs3_2
    by_cases hj3 : j = 3
    · subst hj3; exact hs3_3
    · rw [hframe3 j hj hj1 hj2 hj3, hframe2 j hj hj1 hj2 hj3, hframe1 j hj hj1 hj2 hj3]

/-- `zipWith` field of `HvdH.KernelLib` (v2/v3).  Imports: `Submission.Work.Kernel.Raw`, `Submission.Work.Kernel.Pend`, plus the already-proved marker movers `Submission.Work.Layout.Move` (`Work.Layout.Ev` = bounded `Eval`; `mvVal_ev` moves one value between two stacks at cost `≤ 16*(vsz v+1)`).  Same plan as `mapList`, but the two `cons`-chains are moved aside onto two scratch stacks in lock-step (`xs.length = ys.length`), and per index the element of `xs` and the element of `ys` are brought back on top of `rest` so that `q` sees exactly `x :: y :: rest`; then `q` is run and its result is moved aside; finally `ofList zs` is rebuilt on stack 0.  At `xs = ys = []` both top values are `nil`: drop both and output `.nil` (cost ≤ K).  Key encodings: `encs (ofList xs :: rest) = cons :: (encs xs ++ rest)`, `encs (x :: xs') = x.enc ++ encs xs'`, `ofList [] = .nil`.  Helpers must be named with the prefix `zipWith_`. -/
theorem zipWith : ∃ (comb : HvdH.Cmd → HvdH.Cmd) (K : ℕ), ∀ (main q : HvdH.Cmd) (rest : List HvdH.Val) (P : HvdH.Val → HvdH.Val → Prop)
    (Q : HvdH.Val → HvdH.Val → HvdH.Val → Prop) (c L : ℕ),
    (∀ x y, P x y → HvdH.WordR main q (fun vs => vs = x :: y :: rest)
      (fun _ out => ∃ z, out = z :: rest ∧ Q x y z ∧ HvdH.vsz z ≤ L) (fun _ => c)) →
    ∀ xs ys : List HvdH.Val, xs.length = ys.length →
    (∀ i < xs.length, P (xs.getD i HvdH.Val.nil) (ys.getD i HvdH.Val.nil)) →
    (∀ x ∈ xs ++ ys, HvdH.vsz x ≤ L) →
    HvdH.WordR main (comb q) (fun vs => vs = HvdH.ofList xs :: HvdH.ofList ys :: rest)
      (fun _ out => ∃ zs, out = HvdH.ofList zs :: rest ∧ zs.length = xs.length ∧
        ∀ i < xs.length, Q (xs.getD i HvdH.Val.nil) (ys.getD i HvdH.Val.nil) (zs.getD i HvdH.Val.nil))
      (fun _ => xs.length * (c + K * (L + 1)) + K) := by
  refine ⟨zipWith_prog, 256, ?_⟩
  intro main q rest P Q c L hq xs ys hlen hP hL vs hvs s R hR
  subst hvs
  obtain ⟨p', s', n, hev, hn, hp'len, hcorr, h0', hframe⟩ :=
    zipWith_all_ev main q rest P Q c L hq xs ys s R hlen hP hL hR
  refine ⟨ofList p' :: rest, s', n, ⟨p', rfl, ?_, ?_⟩, hev, ?_, h0', ?_⟩
  · rw [hp'len]
  · intro i hi
    exact hcorr i hi
  · exact hn
  · intro k hk
    exact hframe k hk

end Work.Kernel
