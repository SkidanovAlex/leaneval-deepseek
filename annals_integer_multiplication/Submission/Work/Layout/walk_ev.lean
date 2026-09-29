import Mathlib
import Submission.Work.Layout.chunksOfDefs

/-!
# `walkProg` walks the `cons`-chain `ofList ys` off stack 0

`Work.Layout.walkProg` (`Submission/Work/Layout/chunksOfDefs.lean`) is the second phase of
`chunksOf`: it walks the list `ofList ys` on stack 0, moving every element to `sT` with
`Work.Layout.mvVal` (so the last element of the list ends up deepest on `sT`, i.e. `sT` shows
`encs ys.reverse` above a `gSent` sentinel) and leaving the `nil` terminator of the list on
stack 0.  Cost `O(vsz (ofList ys))`.

The proof is a straightforward induction on the list (`walk_loop`), each step being one iteration
of `walkBody_ck` (`walkBody_cons`, `walkBody_nil`), using the full-strength mover
`Work.Layout.mvVal_ev_full` which additionally records that its scratch stacks `sB`, `sC` are
restored, so every stack other than `0`, `sT`, `sB`, `sC` is left untouched.
-/

set_option linter.unusedVariables false

namespace Work.Layout

open HvdH

/-! ## Pure list arithmetic -/

/-- the length of the flattened `cons :: enc` list: one `cons` plus one encoding per element -/
theorem flatMap_cons_enc_length (ys : List Val) :
    ((ys.map fun v => Glyph.cons :: v.enc).flatten).length = (ys.map vsz).sum + ys.length := by
  induction ys with
  | nil => simp
  | cons v ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, ih,
      List.sum_cons, HvdH.vsz]
    ring

/-- the per-element budget of `walk_loop`, summed over the list -/
theorem sum_map_affine (ys : List Val) :
    (ys.map (fun v => 16 * vsz v + 21)).sum = 16 * (ys.map vsz).sum + 21 * ys.length := by
  induction ys with
  | nil => simp
  | cons v ys ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- the accumulated list on `sT` after one more element -/
theorem encs_rev_snoc (u : List Val) (v : Val) :
    (((u ++ [v]).map Val.enc).reverse).flatten = v.enc ++ ((u.map Val.enc).reverse).flatten := by
  simp

/-! ## One iteration of the walking loop -/

/-- One iteration of `walkProg`'s loop, taken on the `nil` terminator: the head of stack 0 is not
a `cons`, so the loop stops (`rLoopG := eos`) and nothing else is touched.  Cost `3` (`peek` plus
the two steps of the `ite`). -/
theorem walkBody_nil {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {A : List Glyph}
    (h0 : X 0 = Glyph.nil :: A) :
    ∃ s' n, Ev main walkBody_ck ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk 0 = Glyph.nil :: A ∧
      s'.reg rLoopG = Glyph.eos ∧ (∀ j : Stk, j ≠ 0 → s'.stk j = X j) := by
  have hpeek : Ev main (.peek 0 rE) ⟨g, X⟩ ⟨Function.update g rE Glyph.nil, X⟩ 1 := by
    have h := ev_peek' main 0 rE g X
    rw [show (X 0).headD Glyph.eos = Glyph.nil from by rw [h0]; rfl] at h
    exact h
  have hite : Ev main
      (.ite rE Glyph.cons (seqs [.pop 0 rE, mvVal 0 sT sB sC, .set rLoopG gCont])
        (.set rLoopG Glyph.eos))
      ⟨Function.update g rE Glyph.nil, X⟩
      ⟨Function.update (Function.update g rE Glyph.nil) rLoopG Glyph.eos, X⟩ 2 :=
    Ev.iteF (by show Function.update g rE Glyph.nil rE ≠ Glyph.cons
                rw [Function.update_self]; decide)
      (ev_set' main rLoopG Glyph.eos _ _)
  refine ⟨⟨Function.update (Function.update g rE Glyph.nil) rLoopG Glyph.eos, X⟩, 3,
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold walkBody_ck
    simp only [seqs]
    exact Ev.seq hpeek hite
  · omega
  · exact h0
  · show Function.update (Function.update g rE Glyph.nil) rLoopG Glyph.eos rLoopG = Glyph.eos
    rw [Function.update_self]
  · intro j _
    rfl

/-- One iteration of `walkProg`'s loop on a `cons`: drop the `cons` glyph, move the following
value `v` from stack 0 to `sT` (via `mvVal`), and keep going (`rLoopG := gCont`).  Cost
`16 * (vsz v + 1) + 4`: `peek` + `ite` + `pop` + `mvVal` + `set`. -/
theorem walkBody_cons {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {v : Val}
    {A : List Glyph} (h0 : X 0 = Glyph.cons :: (v.enc ++ A)) (hg : g rLoopG = gCont) :
    ∃ s' n, Ev main walkBody_ck ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz v + 1) + 4 ∧
      s'.stk 0 = A ∧ s'.stk sT = v.enc ++ X sT ∧ s'.reg rLoopG = gCont ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  have hpeek : Ev main (.peek 0 rE) ⟨g, X⟩ ⟨Function.update g rE Glyph.cons, X⟩ 1 := by
    have h := ev_peek' main 0 rE g X
    rw [show (X 0).headD Glyph.eos = Glyph.cons from by rw [h0]; rfl] at h
    exact h
  have hpop : Ev main (.pop 0 rE) ⟨Function.update g rE Glyph.cons, X⟩
      ⟨Function.update (Function.update g rE Glyph.cons) rE Glyph.cons,
        Function.update X 0 (v.enc ++ A)⟩ 1 := by
    have h := ev_pop' main 0 rE (Function.update g rE Glyph.cons) X
    rw [show (X 0).headD Glyph.eos = Glyph.cons from by rw [h0]; rfl,
        show (X 0).tail = v.enc ++ A from by rw [h0]; rfl] at h
    exact h
  obtain ⟨s₂, n₂, hev₂, hn₂, hA, hS, hB, hC, hfr⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := sT) (c := sB) (d := sC)
      (g := Function.update (Function.update g rE Glyph.cons) rE Glyph.cons)
      (X := Function.update X 0 (v.enc ++ A)) (v := v) (A := A) (B := X sT)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by show Function.update X 0 (v.enc ++ A) 0 = v.enc ++ A
          rw [Function.update_self])
      (by show Function.update X 0 (v.enc ++ A) sT = X sT
          rw [Function.update_of_ne (show sT ≠ (0 : Stk) by decide)])
  have hset : Ev main (.set rLoopG gCont) s₂ ⟨Function.update s₂.reg rLoopG gCont, s₂.stk⟩ 1 :=
    ev_set' main rLoopG gCont s₂.reg s₂.stk
  have h2 : Ev main (.seq (mvVal 0 sT sB sC) (.set rLoopG gCont)) _ _
      (n₂ + 1) := Ev.seq hev₂ hset
  have h1 : Ev main (.seq (.pop 0 rE) (.seq (mvVal 0 sT sB sC) (.set rLoopG gCont))) _ _
      (1 + (n₂ + 1)) := Ev.seq hpop h2
  have hbranch : Ev main (seqs [.pop 0 rE, mvVal 0 sT sB sC, .set rLoopG gCont])
      ⟨Function.update g rE Glyph.cons, X⟩ ⟨Function.update s₂.reg rLoopG gCont, s₂.stk⟩
      (1 + (n₂ + 1)) := by
    simpa only [seqs] using h1
  have hite : Ev main (.ite rE Glyph.cons (seqs [.pop 0 rE, mvVal 0 sT sB sC, .set rLoopG gCont])
        (.set rLoopG Glyph.eos))
      ⟨Function.update g rE Glyph.cons, X⟩ ⟨Function.update s₂.reg rLoopG gCont, s₂.stk⟩
      (1 + (n₂ + 1) + 1) :=
    Ev.iteT (by show Function.update g rE Glyph.cons rE = Glyph.cons
                rw [Function.update_self]) hbranch
  refine ⟨⟨Function.update s₂.reg rLoopG gCont, s₂.stk⟩, 1 + (1 + (n₂ + 1) + 1),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold walkBody_ck
    simp only [seqs]
    exact Ev.seq hpeek hite
  · have h1 : n₂ ≤ 16 * (vsz v + 1) := hn₂
    omega
  · exact hA
  · exact hS
  · show Function.update s₂.reg rLoopG gCont rLoopG = gCont
    rw [Function.update_self]
  · intro j hj0 hjS hjB hjC
    show s₂.stk j = X j
    rw [hfr j hj0 hjS hjB hjC]
    show Function.update X 0 (v.enc ++ A) j = X j
    rw [Function.update_of_ne hj0]

/-! ## The walking loop -/

/-- The walking loop of `walkProg`, run to completion on the list `zs` (the part of the list still
on stack 0) with `u` the elements already moved.  It performs `zs.length + 1` iterations (`+ 1`
for the `nil` terminator) and leaves `nil` (the terminator of the original list) on stack 0,
`encs (u ++ zs).reverse` above `gSent :: T0` on `sT`, and the driver register at `eos`. -/
theorem walk_loop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    (zs u : List Val) (A T0 : List Glyph)
    (h0 : X 0 = (zs.map fun v => Glyph.cons :: v.enc).flatten ++ (Glyph.nil :: A))
    (hT : X sT = ((u.map Val.enc).reverse).flatten ++ gSent :: T0)
    (hg : g rLoopG = gCont) :
    ∃ s' C, loopRuns main rLoopG gCont walkBody_ck (zs.length + 1) ⟨g, X⟩ s' C ∧
      C ≤ 4 + (zs.map (fun v => 16 * vsz v + 21)).sum ∧
      s'.stk 0 = Glyph.nil :: A ∧
      s'.stk sT = (((u ++ zs).map Val.enc).reverse).flatten ++ gSent :: T0 ∧
      s'.reg rLoopG = Glyph.eos ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  induction zs generalizing u g X with
  | nil =>
      have h0' : X 0 = Glyph.nil :: A := by simpa using h0
      obtain ⟨s', n, hev, hn, hstk, hreg, hfr⟩ :=
        walkBody_nil (main := main) (g := g) (X := X) h0'
      refine ⟨s', 4, loopRuns.one hg (hev.mono hn), ?_, hstk, ?_, hreg, ?_⟩
      · simp
      · rw [hfr sT (by decide), hT]; simp
      · intro j hj0 _ _ _
        exact hfr j hj0
  | cons v t ih =>
      have h0' : X 0 = Glyph.cons :: (v.enc ++ ((t.map fun w => Glyph.cons :: w.enc).flatten
          ++ (Glyph.nil :: A))) := by
        rw [h0]
        simp only [List.map_cons, List.flatten_cons, List.cons_append, List.append_assoc]
      obtain ⟨s₁, n₁, hev₁, hn₁, hstk₁, hstkS₁, hreg₁, hfr₁⟩ :=
        walkBody_cons (main := main) (g := g) (X := X) (v := v)
          (A := (t.map fun w => Glyph.cons :: w.enc).flatten ++ (Glyph.nil :: A)) h0' hg
      have hT₁ : s₁.stk sT = (((u ++ [v]).map Val.enc).reverse).flatten ++ gSent :: T0 := by
        rw [hstkS₁, hT, encs_rev_snoc u v]
        simp only [List.append_assoc]
      obtain ⟨s₂, C₂, hrun₂, hC₂, hstk₂, hstkS₂, hreg₂, hfr₂⟩ :=
        ih (g := s₁.reg) (X := s₁.stk) (u ++ [v]) hstk₁ hT₁ hreg₁
      have hC : (16 * (vsz v + 1) + 4) + C₂ + 1 ≤
          4 + ((v :: t).map (fun w => 16 * vsz w + 21)).sum := by
        have h2 := hC₂
        simp only [List.map_cons, List.sum_cons]
        omega
      refine ⟨s₂, (16 * (vsz v + 1) + 4) + C₂ + 1,
        loopRuns.succ' (C := (16 * (vsz v + 1) + 4) + C₂ + 1) hg (hev₁.mono hn₁) hrun₂
          (le_refl _), hC, hstk₂, ?_, hreg₂, ?_⟩
      · simpa [List.append_assoc] using hstkS₂
      · intro j hj0 hjT hjB hjC
        rw [hfr₂ j hj0 hjT hjB hjC, hfr₁ j hj0 hjT hjB hjC]

/-- Requires the import of `Submission.Work.Layout.chunksOfDefs`.

`walkProg` walks the list `ofList ys` on stack 0 (first element deepest), moving every element to
`sT` with `Work.Layout.mvVal` (`Submission/Work/Layout/mvVal_ev_full`) and leaving `nil` on stack 0.
Cost `O(vsz (ofList ys))`.  Use `Work.Layout.enc_ofList_cons` / `Work.Layout.headD_enc_ofList` for
the structure of the list on stack 0. -/
theorem walk_ev {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {ys : List HvdH.Val} {A T0 : List HvdH.Glyph}
    (h0 : X 0 = (HvdH.ofList ys).enc ++ A) (hT : X Work.Layout.sT = T0) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.walkProg ⟨g, X⟩ s' n ∧
      n ≤ 40 * (HvdH.vsz (HvdH.ofList ys) + 1) ∧
      s'.stk 0 = [HvdH.Glyph.nil] ++ A ∧
      s'.stk Work.Layout.sT =
        ((ys.map HvdH.Val.enc).reverse).flatten ++ Work.Layout.gSent :: T0 ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.Layout.sT → j ≠ Work.Layout.sB →
        j ≠ Work.Layout.sC → s'.stk j = X j) := by
  have hpk : Ev main (pushK sT gSent) ⟨g, X⟩
      ⟨Function.update g rE gSent, Function.update X sT (gSent :: X sT)⟩ 2 := by
    have h1 : Ev main (.set rE gSent) ⟨g, X⟩ ⟨Function.update g rE gSent, X⟩ 1 :=
      ev_set' main rE gSent g X
    have h3 : Ev main (.push sT rE) ⟨Function.update g rE gSent, X⟩
        ⟨Function.update g rE gSent, Function.update X sT (gSent :: X sT)⟩ 1 := by
      have h := ev_push' main sT rE (Function.update g rE gSent) X
      rwa [Function.update_self] at h
    unfold pushK
    exact Ev.seq h1 h3
  have hset : Ev main (.set rLoopG gCont)
      ⟨Function.update g rE gSent, Function.update X sT (gSent :: X sT)⟩
      ⟨Function.update (Function.update g rE gSent) rLoopG gCont,
        Function.update X sT (gSent :: X sT)⟩ 1 :=
    ev_set' main rLoopG gCont _ _
  have h0' : Function.update X sT (gSent :: X sT) 0 =
      (ys.map fun v => Glyph.cons :: v.enc).flatten ++ (Glyph.nil :: A) := by
    rw [Function.update_of_ne (show (0 : Stk) ≠ sT by decide), h0, enc_ofList_eq]
    simp only [List.append_assoc, List.singleton_append]
  have hT' : Function.update X sT (gSent :: X sT) sT =
      ((([] : List Val).map Val.enc).reverse).flatten ++ gSent :: T0 := by
    rw [Function.update_self, hT]
    simp
  have hg' : Function.update (Function.update g rE gSent) rLoopG gCont rLoopG = gCont := by
    rw [Function.update_self]
  obtain ⟨s₁, C, hrun, hC, hstk0, hstkS, hreg, hfr⟩ :=
    walk_loop (main := main) (g := Function.update (Function.update g rE gSent) rLoopG gCont)
      (X := Function.update X sT (gSent :: X sT)) ys [] A T0 h0' hT' hg'
  have hloop : Ev main (.loop rLoopG gCont walkBody_ck)
      ⟨Function.update (Function.update g rE gSent) rLoopG gCont,
        Function.update X sT (gSent :: X sT)⟩ s₁ (C + 1) :=
    loopRuns.eval hrun (by rw [hreg]; decide)
  have hmain : Ev main walkProg ⟨g, X⟩ s₁ (2 + (1 + (C + 1))) := by
    unfold walkProg
    simp only [seqs]
    exact Ev.seq hpk (Ev.seq hset hloop)
  refine ⟨s₁, 2 + (1 + (C + 1)), hmain, ?_, ?_, ?_, ?_⟩
  · have hflat := flatMap_cons_enc_length ys
    have hsum := sum_map_affine ys
    have hvsz : vsz (ofList ys) + 1 =
        ((ys.map fun v => Glyph.cons :: v.enc).flatten).length + 2 := by
      simp only [HvdH.vsz, enc_ofList_eq, List.length_append, List.length_cons, List.length_nil]
    rw [hsum] at hC
    rw [hvsz, hflat]
    omega
  · simpa using hstk0
  · simpa using hstkS
  · intro j hj0 hjT hjB hjC
    rw [hfr j hj0 hjT hjB hjC]
    exact stkFn_ne X hjT (gSent :: X sT)

end Work.Layout
