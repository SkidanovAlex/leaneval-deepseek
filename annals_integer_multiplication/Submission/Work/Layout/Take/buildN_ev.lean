import Mathlib
import Submission.Work.Layout.Take.Basic
import Submission.Work.Layout.Take.buildNBody_go
import Submission.Work.Layout.mvVal_ev_full

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Work.Layout.Take

open HvdH

/-! ## Elementary facts about `ofList` -/

/-- `ofList` unfolds at a `cons`. -/
theorem ofList_cons_eq (v : Val) (acc : List Val) :
    ofList (v :: acc) = Val.cons v (ofList acc) := rfl

/-- The encoding of `ofList (v :: acc)`. -/
theorem enc_ofList_cons (v : Val) (acc : List Val) :
    (ofList (v :: acc)).enc = Glyph.cons :: (v.enc ++ (ofList acc).enc) := rfl

/-- `n ≤ (zs.take n).map vsz).sum` when `n ≤ zs.length`: every value uses at least one glyph. -/
theorem le_sum_vsz_take_buildN (zs : List Val) (n : ℕ) (hn : n ≤ zs.length) :
    n ≤ ((zs.take n).map vsz).sum := by
  have hlen : (zs.take n).length = n := by rw [List.length_take, Nat.min_eq_left hn]
  have hle : (zs.take n).length ≤ ((zs.take n).map vsz).sum := by
    have h := List.length_le_sum_of_one_le ((zs.take n).map vsz) (fun i hi => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hi
      exact Work.Layout.one_le_vsz v)
    rwa [List.length_map] at h
  omega

/-! ## One iteration of the rebuild loop, and the loop itself -/

/-- One iteration of `Work.Layout.buildNProg`'s loop on an exhausted counter: the top of the
counter stack `c` is the frame marker `gMark`, so `Work.Layout.buildNBody` takes its `else` branch
and only sets the driver register `rG` to `eos` (cost `3`); no stack is touched. -/
theorem buildNBody_stop (main : HvdH.Cmd) (c b : HvdH.Stk) {Crest : List HvdH.Glyph}
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph}
    (hc : X c = Work.Layout.gMark :: Crest) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.buildNBody c b) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.reg Work.Layout.rG = HvdH.Glyph.eos ∧ (∀ j, s'.stk j = X j) := by
  have hhead : (X c).headD Glyph.eos = Work.Layout.gMark := by rw [hc]; rfl
  have hpeek : Ev main (.peek c Work.Layout.rE_x) ⟨g, X⟩
      ⟨Function.update g Work.Layout.rE_x Work.Layout.gMark, X⟩ 1 := by
    have h := ev_peek' main c Work.Layout.rE_x g X
    rw [hhead] at h
    exact h
  have hne : (Function.update g Work.Layout.rE_x Work.Layout.gMark) Work.Layout.rE_x
      ≠ Work.Layout.gU := by
    rw [Function.update_self]
    exact Work.Layout.gMark_ne_gU
  have hset : Ev main (.set Work.Layout.rG Glyph.eos)
      ⟨Function.update g Work.Layout.rE_x Work.Layout.gMark, X⟩
      ⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gMark)
        Work.Layout.rG Glyph.eos, X⟩ 1 :=
    ev_set' main Work.Layout.rG Glyph.eos _ _
  have hite : Ev main
      (.ite Work.Layout.rE_x Work.Layout.gU
        (seqs [.pop c Work.Layout.rE_x, mvVal b 0 Work.Layout.sX Work.Layout.sY,
          .set Work.Layout.rE_x Glyph.cons, .push 0 Work.Layout.rE_x,
          .set Work.Layout.rG Work.Layout.gCont_x])
        (.set Work.Layout.rG Glyph.eos))
      ⟨Function.update g Work.Layout.rE_x Work.Layout.gMark, X⟩
      ⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gMark)
        Work.Layout.rG Glyph.eos, X⟩ 2 :=
    Ev.iteF hne hset
  have hbody : Ev main (Work.Layout.buildNBody c b) ⟨g, X⟩
      ⟨Function.update (Function.update g Work.Layout.rE_x Work.Layout.gMark)
        Work.Layout.rG Glyph.eos, X⟩ 3 := by
    unfold Work.Layout.buildNBody
    simp only [seqs]
    exact Ev.seq hpeek hite
  refine ⟨_, _, hbody, by omega, ?_, ?_⟩
  · show Function.update (Function.update g Work.Layout.rE_x Work.Layout.gMark)
      Work.Layout.rG Glyph.eos Work.Layout.rG = Glyph.eos
    rw [Function.update_self]
  · intro j
    rfl

/-- The rebuild loop of `Work.Layout.buildNProg`: it makes `n + 1` iterations (the last one only
stops), consuming the `n` unary units of the counter stack `c` and moving the first `n` values of
`b` (which shows `zs`) onto stack `0`, each in front of a fresh `cons`.  Since the first value moved
lands deepest, stack `0` ends up showing `ofList ((zs.take n).reverse ++ acc)`, where `acc` is the
list the accumulator already showed. -/
theorem buildNLoop (main : HvdH.Cmd) (c b : HvdH.Stk) (hc0 : c ≠ 0) (hb0 : b ≠ 0)
    (hbc : c ≠ b) (hbX : b ≠ Work.Layout.sX) (hbY : b ≠ Work.Layout.sY)
    (hcX : c ≠ Work.Layout.sX) (hcY : c ≠ Work.Layout.sY) :
    ∀ (n : ℕ) (zs acc : List HvdH.Val), n ≤ zs.length →
      ∀ (Brest Crest R : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
        (X : HvdH.Stk → List HvdH.Glyph),
        X b = HvdH.encs zs ++ Work.Layout.gMark :: Brest →
        X c = List.replicate n Work.Layout.gU ++ Work.Layout.gMark :: Crest →
        X 0 = (HvdH.ofList acc).enc ++ R → g Work.Layout.rG = Work.Layout.gCont_x →
        ∃ s', Work.Layout.loopRuns main Work.Layout.rG Work.Layout.gCont_x
            (Work.Layout.buildNBody c b) (n + 1) ⟨g, X⟩ s'
            (16 * (((zs.take n).map HvdH.vsz).sum) + 23 * n + 4) ∧
          s'.stk c = Work.Layout.gMark :: Crest ∧
          s'.stk b = HvdH.encs (zs.drop n) ++ Work.Layout.gMark :: Brest ∧
          s'.stk 0 = (HvdH.ofList ((zs.take n).reverse ++ acc)).enc ++ R ∧
          s'.reg Work.Layout.rG = HvdH.Glyph.eos ∧
          s'.stk Work.Layout.sX = X Work.Layout.sX ∧
          s'.stk Work.Layout.sY = X Work.Layout.sY ∧
          (∀ j, j ≠ c → j ≠ b → j ≠ 0 → j ≠ Work.Layout.sX → j ≠ Work.Layout.sY →
            s'.stk j = X j) := by
  intro n
  induction n with
  | zero =>
      intro zs acc _ Brest Crest R g X hB hC h0 hg
      have hC0 : X c = Work.Layout.gMark :: Crest := by simpa using hC
      obtain ⟨s', n', hev, hn', hrG, hstk⟩ :=
        buildNBody_stop main c b (Crest := Crest) (g := g) (X := X) hC0
      refine ⟨s',
        loopRuns.mono (by omega) (loopRuns.one hg (hev.mono hn')) (by simp), ?_, ?_, ?_,
        hrG, ?_, ?_, ?_⟩
      · rw [hstk c]; exact hC0
      · rw [hstk b, hB]; simp
      · rw [hstk 0, h0, List.take_zero, List.reverse_nil, List.nil_append]
      · rw [hstk Work.Layout.sX]
      · rw [hstk Work.Layout.sY]
      · intro j _ _ _ _ _
        exact hstk j
  | succ n ih =>
      intro zs acc hn Brest Crest R g X hB hC h0 hg
      cases zs with
      | nil => simp at hn
      | cons v rest =>
          have hn' : n ≤ rest.length := by simp only [List.length_cons] at hn; omega
          have hB1 : X b = v.enc ++ (HvdH.encs rest ++ Work.Layout.gMark :: Brest) := by
            rw [hB, Work.Kernel.encs_cons, List.append_assoc]
          have hC1 : X c = Work.Layout.gU :: (List.replicate n Work.Layout.gU ++
              Work.Layout.gMark :: Crest) := by
            rw [hC, List.replicate_succ, List.cons_append]
          obtain ⟨s1, m1, hev1, hm1, hc1, hb1, h01, hr1, hX1, hY1, hfr1⟩ :=
            buildNBody_go main c b hc0 hb0 hbc hbX hbY hcX hcY (v := v)
              (C := List.replicate n Work.Layout.gU ++ Work.Layout.gMark :: Crest)
              (B := HvdH.encs rest ++ Work.Layout.gMark :: Brest)
              (A := (HvdH.ofList acc).enc ++ R) hC1 hB1 h0
          have hev1' : Ev main (Work.Layout.buildNBody c b) ⟨g, X⟩ s1
              (16 * (HvdH.vsz v + 1) + 6) := hev1.mono hm1
          have h01' : s1.stk 0 = (HvdH.ofList (v :: acc)).enc ++ R := by
            rw [h01, enc_ofList_cons, List.cons_append, List.append_assoc]
          obtain ⟨s2, hrun2, hc2, hb2, h02, hr2, hX2, hY2, hfr2⟩ :=
            ih rest (v :: acc) hn' Brest Crest R s1.reg s1.stk hb1 hc1 h01' hr1
          have hcat := loopRuns.concat (n + 1) (loopRuns.one hg hev1') hrun2
          have hcost : (16 * (HvdH.vsz v + 1) + 6 + 1) +
                (16 * ((rest.take n).map HvdH.vsz).sum + 23 * n + 4) ≤
              16 * ((((v :: rest).take (n + 1)).map HvdH.vsz).sum) + 23 * (n + 1) + 4 := by
            rw [List.take_succ_cons, List.map_cons, List.sum_cons]
            omega
          refine ⟨s2,
            loopRuns.mono (by omega)
              (loopRuns.cast (show 1 + (n + 1) = (n + 1) + 1 by omega) hcat) hcost,
            hc2, ?_, ?_, hr2, ?_, ?_, ?_⟩
          · rw [List.drop_succ_cons]; exact hb2
          · rw [List.take_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
            exact h02
          · rw [hX2, hX1]
          · rw [hY2, hY1]
          · intro j hjc hjb hj0 hjX hjY
            rw [hfr2 j hjc hjb hj0 hjX hjY, hfr1 j hjc hjb hj0 hjX hjY]

/-- `buildNProg c b` (`Submission/Work/Layout/Take/Defs.lean`) rebuilds `ofList` of the first `n`
elements of the stack `b` (which shows `zs`, i.e. `X b = encs zs ++ gMark :: Brest`), driven by `n`
unary units on the counter stack `c`.  Stack `0` starts as `R`; the result is
`ofList ((zs.take n).reverse)` in front of it, because the first element moved (`zs[0]`) lands
deepest and each element gets a `cons` glyph in front of it.  The counter/carrier stacks used by
this phase (`c`, `b`), the value stack `0` and `mvVal`'s scratch stacks `sX`, `sY` are all
distinct in the intended applications, hence the hypotheses `hc0`, `hb0`, `hbc`, `hbX`, `hbY`,
`hcX`, `hcY`.

Useful: `Work.Layout.mvVal_ev` (in `Submission/Work/Layout/Move.lean`) moves one value from `b` to
stack `0`; it restores its own scratch stacks `sX`, `sY` only through `mvA_ev`/`mvB_ev` (see the
proof of `mvVal_ev`, or the stronger `mvVal_ev_full` if it is in the workspace), so a stronger
variant may have to be proved.  Also `HvdH.encs_append`, `Work.Layout.one_le_vsz`,
`Work.Layout.gMark_notMem_encs`, the `Ev` primitives of `Submission/Work/Layout/Base.lean`. -/
theorem buildN_ev (main : HvdH.Cmd) (c b : HvdH.Stk) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hbc : c ≠ b)
    (hbX : b ≠ Work.Layout.sX) (hbY : b ≠ Work.Layout.sY) (hcX : c ≠ Work.Layout.sX)
    (hcY : c ≠ Work.Layout.sY)
    (zs : List HvdH.Val) (n : ℕ) (hn : n ≤ zs.length)
    (R Brest Crest : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
    (X : HvdH.Stk → List HvdH.Glyph)
    (h0 : X 0 = R) (hB : X b = HvdH.encs zs ++ Work.Layout.gMark :: Brest)
    (hC : X c = List.replicate n Work.Layout.gU ++ Work.Layout.gMark :: Crest) :
    ∃ s' m, Work.Layout.Ev main (Work.Layout.buildNProg c b) ⟨g, X⟩ s' m ∧
      m ≤ 20 * (((zs.take n).map HvdH.vsz).sum + n + 1) ∧
      s'.stk 0 = (HvdH.ofList ((zs.take n).reverse)).enc ++ R ∧
      s'.stk b = HvdH.encs (zs.drop n) ++ Work.Layout.gMark :: Brest ∧
      s'.stk c = Work.Layout.gMark :: Crest ∧
      (∀ j, j ≠ 0 → j ≠ b → j ≠ c → s'.stk j = X j) := by
  -- the initialisation: `set rE_x nil ;; push 0 rE_x ;; set rG gCont_x`
  have h1 : Ev main (.set Work.Layout.rE_x Glyph.nil) ⟨g, X⟩
      ⟨Function.update g Work.Layout.rE_x Glyph.nil, X⟩ 1 :=
    ev_set' main Work.Layout.rE_x Glyph.nil g X
  have h2 : Ev main (.push (0 : HvdH.Stk) Work.Layout.rE_x)
      ⟨Function.update g Work.Layout.rE_x Glyph.nil, X⟩
      ⟨Function.update g Work.Layout.rE_x Glyph.nil,
        Function.update X 0 (Glyph.nil :: X 0)⟩ 1 := by
    have h := ev_push' main (0 : HvdH.Stk) Work.Layout.rE_x
      (Function.update g Work.Layout.rE_x Glyph.nil) X
    rwa [Function.update_self] at h
  have h3 : Ev main (.set Work.Layout.rG Work.Layout.gCont_x)
      ⟨Function.update g Work.Layout.rE_x Glyph.nil,
        Function.update X 0 (Glyph.nil :: X 0)⟩
      ⟨Function.update (Function.update g Work.Layout.rE_x Glyph.nil) Work.Layout.rG
        Work.Layout.gCont_x, Function.update X 0 (Glyph.nil :: X 0)⟩ 1 :=
    ev_set' main Work.Layout.rG Work.Layout.gCont_x _ _
  -- the loop
  have hBl : (Function.update X 0 (Glyph.nil :: X 0)) b =
      HvdH.encs zs ++ Work.Layout.gMark :: Brest := by
    rw [Function.update_of_ne hb0, hB]
  have hCl : (Function.update X 0 (Glyph.nil :: X 0)) c =
      List.replicate n Work.Layout.gU ++ Work.Layout.gMark :: Crest := by
    rw [Function.update_of_ne hc0, hC]
  have h0l : (Function.update X 0 (Glyph.nil :: X 0)) 0 =
      (HvdH.ofList ([] : List HvdH.Val)).enc ++ R := by
    rw [Function.update_self, h0]
    rfl
  have hgl : (Function.update (Function.update g Work.Layout.rE_x Glyph.nil) Work.Layout.rG
      Work.Layout.gCont_x) Work.Layout.rG = Work.Layout.gCont_x := by
    rw [Function.update_self]
  obtain ⟨s1, hrun, hc1, hb1, h01, hr1, hXs, hYs, hfr⟩ :=
    buildNLoop main c b hc0 hb0 hbc hbX hbY hcX hcY n zs ([] : List HvdH.Val) hn
      Brest Crest R (Function.update (Function.update g Work.Layout.rE_x Glyph.nil)
        Work.Layout.rG Work.Layout.gCont_x) (Function.update X 0 (Glyph.nil :: X 0))
      hBl hCl h0l hgl
  have hloop : Ev main (.loop Work.Layout.rG Work.Layout.gCont_x (Work.Layout.buildNBody c b))
      ⟨Function.update (Function.update g Work.Layout.rE_x Glyph.nil) Work.Layout.rG
        Work.Layout.gCont_x, Function.update X 0 (Glyph.nil :: X 0)⟩ s1
      (16 * (((zs.take n).map HvdH.vsz).sum) + 23 * n + 4 + 1) :=
    loopRuns.eval hrun (by rw [hr1]; decide)
  have h3loop : Ev main (.seq (.set Work.Layout.rG Work.Layout.gCont_x)
        (.loop Work.Layout.rG Work.Layout.gCont_x (Work.Layout.buildNBody c b)))
      ⟨Function.update g Work.Layout.rE_x Glyph.nil,
        Function.update X 0 (Glyph.nil :: X 0)⟩ s1
      (1 + (16 * (((zs.take n).map HvdH.vsz).sum) + 23 * n + 4 + 1)) :=
    Ev.seq h3 hloop
  have h23 : Ev main (.seq (.push (0 : HvdH.Stk) Work.Layout.rE_x)
        (.seq (.set Work.Layout.rG Work.Layout.gCont_x)
          (.loop Work.Layout.rG Work.Layout.gCont_x (Work.Layout.buildNBody c b))))
      ⟨Function.update g Work.Layout.rE_x Glyph.nil, X⟩ s1
      (1 + (1 + (16 * (((zs.take n).map HvdH.vsz).sum) + 23 * n + 4 + 1))) :=
    Ev.seq h2 h3loop
  have hmain : Ev main (Work.Layout.buildNProg c b) ⟨g, X⟩ s1
      (1 + (1 + (1 + (16 * (((zs.take n).map HvdH.vsz).sum) + 23 * n + 4 + 1)))) := by
    unfold Work.Layout.buildNProg
    simp only [seqs]
    exact Ev.seq h1 h23
  have hbnd : (1 + (1 + (1 + (16 * (((zs.take n).map HvdH.vsz).sum) + 23 * n + 4 + 1))))
      ≤ 20 * (((zs.take n).map HvdH.vsz).sum + n + 1) := by
    have hsum := le_sum_vsz_take_buildN zs n hn
    omega
  have hs0 : ∀ j, j ≠ 0 → (Function.update X 0 (Glyph.nil :: X 0)) j = X j :=
    fun j hj => Function.update_of_ne hj _ _
  refine ⟨s1, 20 * (((zs.take n).map HvdH.vsz).sum + n + 1), hmain.mono hbnd, le_rfl,
    ?_, ?_, ?_, ?_⟩
  · rw [h01, List.append_nil]
  · exact hb1
  · exact hc1
  · intro j hj0 hjb hjc
    rw [← hs0 j hj0]
    rcases eq_or_ne j Work.Layout.sX with hjX | hjX
    · rw [hjX, hXs]
    rcases eq_or_ne j Work.Layout.sY with hjY | hjY
    · rw [hjY, hYs]
    · rw [hfr j hjc hjb hj0 hjX hjY]

end Work.Layout.Take
