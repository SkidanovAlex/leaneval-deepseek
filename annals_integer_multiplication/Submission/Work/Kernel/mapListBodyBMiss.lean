import Mathlib
import Submission.Work.Kernel.mapListDefs

namespace Work.Kernel

open HvdH

/-- The head of `v.enc ++ B` is never the boundary marker `gMark` (encodings use only `pos`, `neg`,
`bit`, `iend`, `nil`, `cons`, never a `mk i`). -/
theorem headD_enc_append_ne_gMark (v : HvdH.Val) (B : List HvdH.Glyph) :
    (v.enc ++ B).headD HvdH.Glyph.eos ≠ Work.Layout.gMark := by
  cases v with
  | int z =>
      by_cases hz : z < 0
      · rw [HvdH.Val.enc, if_pos hz, List.cons_append, List.headD_cons]
        exact fun h => Work.Layout.gMark_ne_neg h.symm
      · rw [HvdH.Val.enc, if_neg hz, List.cons_append, List.headD_cons]
        exact fun h => Work.Layout.gMark_ne_pos h.symm
  | nil =>
      rw [HvdH.Val.enc, List.singleton_append, List.headD_cons]
      exact fun h => Work.Layout.gMark_ne_nil h.symm
  | cons a b =>
      rw [HvdH.Val.enc, List.cons_append, List.headD_cons]
      exact fun h => Work.Layout.gMark_ne_cons h.symm

/-- One iteration of the phase-C loop of `mapList`: the top glyph of stack 2 is not the boundary
marker, so `mapList_bodyB q` moves the top value `x` of stack 2 onto stack 0 (making the value
stack exactly `x :: rest`), runs `q` — whose `WordR` spec is `hqx` — and moves the result `y` onto
stack 3.

Cost: `1` (`peek`) `+ 1` (`ite` test) `+ 16 * (vsz x + 1)` (first `mvVal`) `+ c` (`q`)
`+ 16 * (vsz y + 1)` (second `mvVal`) `+ 1` (`set`) `≤ c + 32 * (L + 1) + 3` since
`vsz x ≤ L` and `vsz y ≤ L`. -/
theorem mapListBodyBMiss {main q : HvdH.Cmd} {x : HvdH.Val} {bs' rest : List HvdH.Val}
    {R X2 : List HvdH.Glyph} {Q : HvdH.Val → HvdH.Val → Prop} {c L : ℕ} {s : HvdH.State}
    (hx : HvdH.vsz x ≤ L)
    (hqx : HvdH.WordR main q (fun vs => vs = x :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ HvdH.vsz y ≤ L) (fun _ => c))
    (h2 : s.stk 2 = x.enc ++ (HvdH.encs bs' ++ Work.Layout.gMark :: X2))
    (h0 : s.stk 0 = HvdH.encs rest ++ R) :
    ∃ (s' : HvdH.State) (y : HvdH.Val) (C : ℕ),
      Work.Layout.Ev main (Work.Kernel.mapList_bodyB q) s s' C ∧
      C ≤ c + 32 * (L + 1) + 3 ∧
      Q x y ∧ HvdH.vsz y ≤ L ∧
      s'.stk 2 = HvdH.encs bs' ++ Work.Layout.gMark :: X2 ∧
      s'.stk 0 = HvdH.encs rest ++ R ∧
      s'.stk 3 = HvdH.encs [y] ++ s.stk 3 ∧
      s'.reg Work.Layout.rLoopG = HvdH.Glyph.cons ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k) := by
  -- the `ite` test: peek stack 2 into `rA`; its head is the head of `x.enc`, never the marker
  have hpeek : Work.Layout.Ev main (.peek (2 : Stk) Work.Layout.rA) s
      ⟨Function.update s.reg Work.Layout.rA ((s.stk 2).headD Glyph.eos), s.stk⟩ 1 :=
    Work.Layout.ev_peek main 2 Work.Layout.rA s
  have hne : (⟨Function.update s.reg Work.Layout.rA ((s.stk 2).headD Glyph.eos), s.stk⟩ : State).reg
      Work.Layout.rA ≠ Work.Layout.gMark := by
    simp only [Function.update_self]
    rw [h2]
    exact headD_enc_append_ne_gMark x (encs bs' ++ Work.Layout.gMark :: X2)
  -- move the value `x` from stack 2 onto the value stack
  obtain ⟨s2, n1, hmv1, hn1, h1_2, h1_0, h1_4, h1_5, h1_fr⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := (2 : Stk)) (b := (0 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update s.reg Work.Layout.rA ((s.stk 2).headD Glyph.eos)) (X := s.stk)
      (v := x) (A := encs bs' ++ Work.Layout.gMark :: X2) (B := s.stk 0) h2 rfl
  have h2_0 : s2.stk 0 = encs (x :: rest) ++ R := by
    rw [h1_0, h0, encs_cons, List.append_assoc]
  -- run `q`; its `WordR` spec consumes `x :: rest` and produces `y :: rest`
  obtain ⟨out, s3, nq, hPost, hqeval, hnq, h3_0, h3_fr⟩ := hqx (x :: rest) rfl s2 R h2_0
  obtain ⟨y, hout, hQxy, hyvsz⟩ := hPost
  have h3_0' : s3.stk 0 = y.enc ++ (encs rest ++ R) := by
    rw [h3_0, hout, encs_cons, List.append_assoc]
  -- move the result `y` from the value stack onto stack 3
  obtain ⟨s4, n2, hmv2, hn2, h4_0, h4_3, h4_4, h4_5, h4_fr⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := (0 : Stk)) (b := (3 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s3.reg) (X := s3.stk) (v := y) (A := encs rest ++ R) (B := s3.stk 3) h3_0' rfl
  -- reset the loop flag
  have hset : Work.Layout.Ev main (.set Work.Layout.rLoopG Glyph.cons) s4
      (State.tSet s4 Work.Layout.rLoopG Glyph.cons) 1 :=
    Work.Layout.ev_set main Work.Layout.rLoopG Glyph.cons s4
  -- assemble the whole run
  have hInner : Work.Layout.Ev main
      (.seq (Work.Layout.mvVal (0 : Stk) (3 : Stk) (4 : Stk) (5 : Stk))
        (.set Work.Layout.rLoopG Glyph.cons))
      s3 (State.tSet s4 Work.Layout.rLoopG Glyph.cons) (n2 + 1) :=
    Work.Layout.Ev.seq hmv2 hset
  have hMid : Work.Layout.Ev main
      (.seq q (.seq (Work.Layout.mvVal (0 : Stk) (3 : Stk) (4 : Stk) (5 : Stk))
        (.set Work.Layout.rLoopG Glyph.cons)))
      s2 (State.tSet s4 Work.Layout.rLoopG Glyph.cons) (nq + (n2 + 1)) :=
    Work.Layout.Ev.seq ⟨nq, hqeval, le_rfl⟩ hInner
  have hMiss : Work.Layout.Ev main
      (.seq (Work.Layout.mvVal (2 : Stk) (0 : Stk) (4 : Stk) (5 : Stk))
        (.seq q (.seq (Work.Layout.mvVal (0 : Stk) (3 : Stk) (4 : Stk) (5 : Stk))
          (.set Work.Layout.rLoopG Glyph.cons))))
      ⟨Function.update s.reg Work.Layout.rA ((s.stk 2).headD Glyph.eos), s.stk⟩
      (State.tSet s4 Work.Layout.rLoopG Glyph.cons) (n1 + (nq + (n2 + 1))) :=
    Work.Layout.Ev.seq hmv1 hMid
  have hIte : Work.Layout.Ev main
      (.ite Work.Layout.rA Work.Layout.gMark (.set Work.Layout.rLoopG Glyph.eos)
        (.seq (Work.Layout.mvVal (2 : Stk) (0 : Stk) (4 : Stk) (5 : Stk))
          (.seq q (.seq (Work.Layout.mvVal (0 : Stk) (3 : Stk) (4 : Stk) (5 : Stk))
            (.set Work.Layout.rLoopG Glyph.cons)))))
      ⟨Function.update s.reg Work.Layout.rA ((s.stk 2).headD Glyph.eos), s.stk⟩
      (State.tSet s4 Work.Layout.rLoopG Glyph.cons) (n1 + (nq + (n2 + 1)) + 1) :=
    Work.Layout.Ev.iteF hne hMiss
  have hBody : Work.Layout.Ev main (mapList_bodyB q) s
      (State.tSet s4 Work.Layout.rLoopG Glyph.cons) (1 + (n1 + (nq + (n2 + 1)) + 1)) := by
    unfold mapList_bodyB
    exact Work.Layout.Ev.seq hpeek hIte
  have hnq' : nq ≤ c := hnq
  have hbound : 1 + (n1 + (nq + (n2 + 1)) + 1) ≤ c + 32 * (L + 1) + 3 := by omega
  refine ⟨State.tSet s4 Work.Layout.rLoopG Glyph.cons, y, c + 32 * (L + 1) + 3,
    hBody.mono hbound, le_rfl, hQxy, hyvsz, ?_, ?_, ?_, ?_, ?_⟩
  · show s4.stk 2 = encs bs' ++ Work.Layout.gMark :: X2
    rw [h4_fr 2 (by decide) (by decide) (by decide) (by decide), h3_fr 2 (by decide), h1_2]
  · show s4.stk 0 = encs rest ++ R
    exact h4_0
  · show s4.stk 3 = encs [y] ++ s.stk 3
    rw [h4_3, h3_fr 3 (by decide), h1_fr 3 (by decide) (by decide) (by decide) (by decide),
      mapList_encs_singleton]
  · simp [State.tSet, State.updReg]
  · intro k hk0 hk2 hk3
    show s4.stk k = s.stk k
    rcases eq_or_ne k (4 : Stk) with h4 | h4
    · rw [h4, h4_4, h3_fr 4 (by decide), h1_4]
    · rcases eq_or_ne k (5 : Stk) with h5 | h5
      · rw [h5, h4_5, h3_fr 5 (by decide), h1_5]
      · rw [h4_fr k hk0 hk3 h4 h5, h3_fr k hk0, h1_fr k hk2 hk0 h4 h5]

end Work.Kernel
